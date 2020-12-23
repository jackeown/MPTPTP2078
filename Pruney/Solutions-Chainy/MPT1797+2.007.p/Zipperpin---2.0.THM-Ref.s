%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Jcfxmgv8k

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:53 EST 2020

% Result     : Theorem 4.39s
% Output     : Refutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :  302 (31742 expanded)
%              Number of leaves         :   47 (9002 expanded)
%              Depth                    :   37
%              Number of atoms          : 3541 (860306 expanded)
%              Number of equality atoms :   95 (7671 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ X27 ) ) ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k7_tmap_1 @ X23 @ X22 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X28 ) )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X34 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X34 ) @ ( u1_pre_topc @ X34 ) )
        = ( k6_tmap_1 @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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

thf(t63_pre_topc,axiom,(
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
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X7 @ X6 @ X4 )
      | ( v5_pre_topc @ X5 @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ( X7 != X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ( v5_pre_topc @ X5 @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ~ ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
        | ~ ( v5_pre_topc @ X1 @ X0 @ sk_A )
        | ( v5_pre_topc @ X1 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('42',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('43',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v5_pre_topc @ X1 @ X0 @ sk_A )
        | ( v5_pre_topc @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39','40','41','42','43'])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v5_pre_topc @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v5_pre_topc @ X1 @ X0 @ sk_A )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('47',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('51',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['51','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['50','54'])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('58',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('59',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('60',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('61',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('64',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('66',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('75',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('82',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58','59','60','61','71','72','82'])).

thf('84',plain,
    ( ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','83'])).

thf('85',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('87',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('88',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['93'])).

thf('95',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','94'])).

thf('96',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['47'])).

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

thf('97',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( v5_pre_topc @ X17 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X18 @ X17 @ X16 @ X15 )
      | ~ ( zip_tseitin_2 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('100',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( ( k2_struct_0 @ B )
          = k1_xboole_0 )
       => ( ( k2_struct_0 @ A )
          = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('102',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( ( k2_struct_0 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('103',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['52'])).

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

thf('104',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('105',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('108',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('109',plain,(
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

thf('110',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('111',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','116'])).

thf('118',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('119',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('120',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('121',plain,
    ( ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['93'])).

thf('123',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','123'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('125',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('127',plain,
    ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['114','115'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('129',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('130',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','130'])).

thf('132',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['124','131'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('134',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ sk_A )
          = k1_xboole_0 )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('137',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X13 @ X10 ) @ X12 )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( zip_tseitin_1 @ X10 @ X13 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','140'])).

thf('142',plain,
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

thf('143',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X32 != X30 )
      | ( v3_pre_topc @ X32 @ ( k6_tmap_1 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X31 @ X30 ) ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('144',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X31 @ X30 ) ) ) )
      | ( v3_pre_topc @ X30 @ ( k6_tmap_1 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['141','152'])).

thf('154',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relset_1 @ X1 @ X1 @ ( k6_partfun1 @ X1 ) @ X0 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('157',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','157'])).

thf('159',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','94'])).

thf('160',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('162',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','160','161'])).

thf('163',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('164',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('165',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('168',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','168'])).

thf('170',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( ( k2_struct_0 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('171',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( zip_tseitin_0 @ X0 @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ X0 @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['121','122'])).

thf('174',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('176',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['162','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['141','152'])).

thf('179',plain,
    ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('181',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('182',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('183',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['155','156'])).

thf('184',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B )
      = sk_B )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('186',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('187',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B )
      = sk_B )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','180','181','187'])).

thf('189',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','188'])).

thf('190',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['47'])).

thf('191',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v5_pre_topc @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['45','191'])).

thf('193',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','192'])).

thf('194',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('195',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['193','194','195','196','197'])).

thf('199',plain,
    ( ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['89'])).

thf('200',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('201',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['189'])).

thf('203',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['198','203'])).

thf('205',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('206',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('207',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('210',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('211',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['207','208','209','210','211'])).

thf('213',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( ( k2_struct_0 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('214',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('215',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['51','53'])).

thf('216',plain,
    ( ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['166','167'])).

thf('218',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('220',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('222',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('223',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_A )
      | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['220','223'])).

thf('225',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('227',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('228',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['166','167'])).

thf('230',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_A @ sk_A )
      | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['224','225','226','227','228','229'])).

thf('231',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['213','230'])).

thf('232',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X10 @ X13 @ X11 @ X14 )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relset_1 @ X1 @ X1 @ ( k6_partfun1 @ X1 ) @ X0 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('234',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X0 @ X2 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X10 @ X13 @ X11 @ X14 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) @ X13 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('236',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X1 @ X2 )
      | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ X1 ) ) @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['236'])).

thf('238',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X10 @ X13 @ X11 @ X14 )
      | ( v3_pre_topc @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ X1 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X15 @ X16 @ X17 ) @ X17 @ X16 @ X15 )
      | ( v5_pre_topc @ X17 @ X15 @ X16 )
      | ~ ( zip_tseitin_2 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 )
      | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['231','241'])).

thf('243',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['93'])).

thf('244',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['242','243'])).

thf('245',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['198','203'])).

thf('246',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( ( k2_struct_0 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_A ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,(
    zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['212','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 )
      | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('252',plain,(
    v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    $false ),
    inference(demod,[status(thm)],['204','252'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Jcfxmgv8k
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 4.39/4.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.39/4.58  % Solved by: fo/fo7.sh
% 4.39/4.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.39/4.58  % done 2509 iterations in 4.102s
% 4.39/4.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.39/4.58  % SZS output start Refutation
% 4.39/4.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.39/4.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 4.39/4.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.39/4.58  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 4.39/4.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.39/4.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.39/4.58  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 4.39/4.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 4.39/4.58  thf(sk_A_type, type, sk_A: $i).
% 4.39/4.58  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 4.39/4.58  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 4.39/4.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.39/4.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 4.39/4.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.39/4.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.39/4.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.39/4.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.39/4.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.39/4.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 4.39/4.58  thf(sk_B_type, type, sk_B: $i).
% 4.39/4.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.39/4.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.39/4.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.39/4.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.39/4.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.39/4.58  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.39/4.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 4.39/4.58  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 4.39/4.58  thf(t113_tmap_1, conjecture,
% 4.39/4.58    (![A:$i]:
% 4.39/4.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.39/4.58       ( ![B:$i]:
% 4.39/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.39/4.58           ( ( v3_pre_topc @ B @ A ) <=>
% 4.39/4.58             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 4.39/4.58               ( v1_funct_2 @
% 4.39/4.58                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.39/4.58                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 4.39/4.58               ( v5_pre_topc @
% 4.39/4.58                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 4.39/4.58               ( m1_subset_1 @
% 4.39/4.58                 ( k7_tmap_1 @ A @ B ) @ 
% 4.39/4.58                 ( k1_zfmisc_1 @
% 4.39/4.58                   ( k2_zfmisc_1 @
% 4.39/4.58                     ( u1_struct_0 @ A ) @ 
% 4.39/4.58                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 4.39/4.58  thf(zf_stmt_0, negated_conjecture,
% 4.39/4.58    (~( ![A:$i]:
% 4.39/4.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.39/4.58            ( l1_pre_topc @ A ) ) =>
% 4.39/4.58          ( ![B:$i]:
% 4.39/4.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.39/4.58              ( ( v3_pre_topc @ B @ A ) <=>
% 4.39/4.58                ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 4.39/4.58                  ( v1_funct_2 @
% 4.39/4.58                    ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.39/4.58                    ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 4.39/4.58                  ( v5_pre_topc @
% 4.39/4.58                    ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 4.39/4.58                  ( m1_subset_1 @
% 4.39/4.58                    ( k7_tmap_1 @ A @ B ) @ 
% 4.39/4.58                    ( k1_zfmisc_1 @
% 4.39/4.58                      ( k2_zfmisc_1 @
% 4.39/4.58                        ( u1_struct_0 @ A ) @ 
% 4.39/4.58                        ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 4.39/4.58    inference('cnf.neg', [status(esa)], [t113_tmap_1])).
% 4.39/4.58  thf('0', plain,
% 4.39/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf(dt_k7_tmap_1, axiom,
% 4.39/4.58    (![A:$i,B:$i]:
% 4.39/4.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.39/4.58         ( l1_pre_topc @ A ) & 
% 4.39/4.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.39/4.58       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 4.39/4.58         ( v1_funct_2 @
% 4.39/4.58           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.39/4.58           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 4.39/4.58         ( m1_subset_1 @
% 4.39/4.58           ( k7_tmap_1 @ A @ B ) @ 
% 4.39/4.58           ( k1_zfmisc_1 @
% 4.39/4.58             ( k2_zfmisc_1 @
% 4.39/4.58               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 4.39/4.58  thf('1', plain,
% 4.39/4.58      (![X26 : $i, X27 : $i]:
% 4.39/4.58         (~ (l1_pre_topc @ X26)
% 4.39/4.58          | ~ (v2_pre_topc @ X26)
% 4.39/4.58          | (v2_struct_0 @ X26)
% 4.39/4.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.39/4.58          | (m1_subset_1 @ (k7_tmap_1 @ X26 @ X27) @ 
% 4.39/4.58             (k1_zfmisc_1 @ 
% 4.39/4.58              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ 
% 4.39/4.58               (u1_struct_0 @ (k6_tmap_1 @ X26 @ X27))))))),
% 4.39/4.58      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 4.39/4.58  thf('2', plain,
% 4.39/4.58      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.58         (k1_zfmisc_1 @ 
% 4.39/4.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 4.39/4.58        | (v2_struct_0 @ sk_A)
% 4.39/4.58        | ~ (v2_pre_topc @ sk_A)
% 4.39/4.58        | ~ (l1_pre_topc @ sk_A))),
% 4.39/4.58      inference('sup-', [status(thm)], ['0', '1'])).
% 4.39/4.58  thf('3', plain,
% 4.39/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf(d10_tmap_1, axiom,
% 4.39/4.58    (![A:$i]:
% 4.39/4.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.39/4.58       ( ![B:$i]:
% 4.39/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.39/4.58           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.39/4.58  thf('4', plain,
% 4.39/4.58      (![X22 : $i, X23 : $i]:
% 4.39/4.58         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 4.39/4.58          | ((k7_tmap_1 @ X23 @ X22) = (k6_partfun1 @ (u1_struct_0 @ X23)))
% 4.39/4.58          | ~ (l1_pre_topc @ X23)
% 4.39/4.58          | ~ (v2_pre_topc @ X23)
% 4.39/4.58          | (v2_struct_0 @ X23))),
% 4.39/4.58      inference('cnf', [status(esa)], [d10_tmap_1])).
% 4.39/4.58  thf('5', plain,
% 4.39/4.58      (((v2_struct_0 @ sk_A)
% 4.39/4.58        | ~ (v2_pre_topc @ sk_A)
% 4.39/4.58        | ~ (l1_pre_topc @ sk_A)
% 4.39/4.58        | ((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 4.39/4.58      inference('sup-', [status(thm)], ['3', '4'])).
% 4.39/4.58  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('8', plain,
% 4.39/4.58      (((v2_struct_0 @ sk_A)
% 4.39/4.58        | ((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 4.39/4.58      inference('demod', [status(thm)], ['5', '6', '7'])).
% 4.39/4.58  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('10', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('11', plain,
% 4.39/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf(t104_tmap_1, axiom,
% 4.39/4.58    (![A:$i]:
% 4.39/4.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.39/4.58       ( ![B:$i]:
% 4.39/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.39/4.58           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 4.39/4.58             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 4.39/4.58  thf('12', plain,
% 4.39/4.58      (![X28 : $i, X29 : $i]:
% 4.39/4.58         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 4.39/4.58          | ((u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)) = (u1_struct_0 @ X29))
% 4.39/4.58          | ~ (l1_pre_topc @ X29)
% 4.39/4.58          | ~ (v2_pre_topc @ X29)
% 4.39/4.58          | (v2_struct_0 @ X29))),
% 4.39/4.58      inference('cnf', [status(esa)], [t104_tmap_1])).
% 4.39/4.58  thf('13', plain,
% 4.39/4.58      (((v2_struct_0 @ sk_A)
% 4.39/4.58        | ~ (v2_pre_topc @ sk_A)
% 4.39/4.58        | ~ (l1_pre_topc @ sk_A)
% 4.39/4.58        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('sup-', [status(thm)], ['11', '12'])).
% 4.39/4.58  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('16', plain,
% 4.39/4.58      (((v2_struct_0 @ sk_A)
% 4.39/4.58        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('demod', [status(thm)], ['13', '14', '15'])).
% 4.39/4.58  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('18', plain,
% 4.39/4.58      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.39/4.58      inference('clc', [status(thm)], ['16', '17'])).
% 4.39/4.58  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('21', plain,
% 4.39/4.58      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.39/4.58         (k1_zfmisc_1 @ 
% 4.39/4.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 4.39/4.58        | (v2_struct_0 @ sk_A))),
% 4.39/4.58      inference('demod', [status(thm)], ['2', '10', '18', '19', '20'])).
% 4.39/4.58  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('23', plain,
% 4.39/4.58      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.39/4.58        (k1_zfmisc_1 @ 
% 4.39/4.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 4.39/4.58      inference('clc', [status(thm)], ['21', '22'])).
% 4.39/4.58  thf('24', plain,
% 4.39/4.58      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('25', plain,
% 4.39/4.58      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.39/4.58      inference('split', [status(esa)], ['24'])).
% 4.39/4.58  thf('26', plain,
% 4.39/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf(t106_tmap_1, axiom,
% 4.39/4.58    (![A:$i]:
% 4.39/4.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.39/4.58       ( ![B:$i]:
% 4.39/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.39/4.58           ( ( v3_pre_topc @ B @ A ) <=>
% 4.39/4.58             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 4.39/4.58               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 4.39/4.58  thf('27', plain,
% 4.39/4.58      (![X33 : $i, X34 : $i]:
% 4.39/4.58         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 4.39/4.58          | ~ (v3_pre_topc @ X33 @ X34)
% 4.39/4.58          | ((g1_pre_topc @ (u1_struct_0 @ X34) @ (u1_pre_topc @ X34))
% 4.39/4.58              = (k6_tmap_1 @ X34 @ X33))
% 4.39/4.58          | ~ (l1_pre_topc @ X34)
% 4.39/4.58          | ~ (v2_pre_topc @ X34)
% 4.39/4.58          | (v2_struct_0 @ X34))),
% 4.39/4.58      inference('cnf', [status(esa)], [t106_tmap_1])).
% 4.39/4.58  thf('28', plain,
% 4.39/4.58      (((v2_struct_0 @ sk_A)
% 4.39/4.58        | ~ (v2_pre_topc @ sk_A)
% 4.39/4.58        | ~ (l1_pre_topc @ sk_A)
% 4.39/4.58        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 4.39/4.58            = (k6_tmap_1 @ sk_A @ sk_B))
% 4.39/4.58        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.39/4.58      inference('sup-', [status(thm)], ['26', '27'])).
% 4.39/4.58  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('31', plain,
% 4.39/4.58      (((v2_struct_0 @ sk_A)
% 4.39/4.58        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 4.39/4.58            = (k6_tmap_1 @ sk_A @ sk_B))
% 4.39/4.58        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.39/4.58      inference('demod', [status(thm)], ['28', '29', '30'])).
% 4.39/4.58  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('33', plain,
% 4.39/4.58      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 4.39/4.58        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 4.39/4.58            = (k6_tmap_1 @ sk_A @ sk_B)))),
% 4.39/4.58      inference('clc', [status(thm)], ['31', '32'])).
% 4.39/4.58  thf('34', plain,
% 4.39/4.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 4.39/4.58          = (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.39/4.58      inference('sup-', [status(thm)], ['25', '33'])).
% 4.39/4.58  thf(t63_pre_topc, axiom,
% 4.39/4.58    (![A:$i]:
% 4.39/4.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.39/4.58       ( ![B:$i]:
% 4.39/4.58         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.39/4.58           ( ![C:$i]:
% 4.39/4.58             ( ( ( v1_funct_1 @ C ) & 
% 4.39/4.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.39/4.58                 ( m1_subset_1 @
% 4.39/4.58                   C @ 
% 4.39/4.58                   ( k1_zfmisc_1 @
% 4.39/4.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.39/4.58               ( ![D:$i]:
% 4.39/4.58                 ( ( ( v1_funct_1 @ D ) & 
% 4.39/4.58                     ( v1_funct_2 @
% 4.39/4.58                       D @ ( u1_struct_0 @ A ) @ 
% 4.39/4.58                       ( u1_struct_0 @
% 4.39/4.58                         ( g1_pre_topc @
% 4.39/4.58                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 4.39/4.58                     ( m1_subset_1 @
% 4.39/4.58                       D @ 
% 4.39/4.58                       ( k1_zfmisc_1 @
% 4.39/4.58                         ( k2_zfmisc_1 @
% 4.39/4.58                           ( u1_struct_0 @ A ) @ 
% 4.39/4.58                           ( u1_struct_0 @
% 4.39/4.58                             ( g1_pre_topc @
% 4.39/4.58                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 4.39/4.58                   ( ( ( C ) = ( D ) ) =>
% 4.39/4.58                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.39/4.58                       ( v5_pre_topc @
% 4.39/4.58                         D @ A @ 
% 4.39/4.58                         ( g1_pre_topc @
% 4.39/4.58                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.39/4.58  thf('35', plain,
% 4.39/4.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 4.39/4.58         (~ (v2_pre_topc @ X4)
% 4.39/4.58          | ~ (l1_pre_topc @ X4)
% 4.39/4.58          | ~ (v1_funct_1 @ X5)
% 4.39/4.58          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ 
% 4.39/4.58               (u1_struct_0 @ 
% 4.39/4.58                (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4))))
% 4.39/4.58          | ~ (m1_subset_1 @ X5 @ 
% 4.39/4.58               (k1_zfmisc_1 @ 
% 4.39/4.58                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ 
% 4.39/4.58                 (u1_struct_0 @ 
% 4.39/4.58                  (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4))))))
% 4.39/4.58          | ~ (v5_pre_topc @ X7 @ X6 @ X4)
% 4.39/4.58          | (v5_pre_topc @ X5 @ X6 @ 
% 4.39/4.58             (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 4.39/4.58          | ((X7) != (X5))
% 4.39/4.58          | ~ (m1_subset_1 @ X7 @ 
% 4.39/4.58               (k1_zfmisc_1 @ 
% 4.39/4.58                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 4.39/4.58          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 4.39/4.58          | ~ (v1_funct_1 @ X7)
% 4.39/4.58          | ~ (l1_pre_topc @ X6)
% 4.39/4.58          | ~ (v2_pre_topc @ X6))),
% 4.39/4.58      inference('cnf', [status(esa)], [t63_pre_topc])).
% 4.39/4.58  thf('36', plain,
% 4.39/4.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.39/4.58         (~ (v2_pre_topc @ X6)
% 4.39/4.58          | ~ (l1_pre_topc @ X6)
% 4.39/4.58          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 4.39/4.58          | ~ (m1_subset_1 @ X5 @ 
% 4.39/4.58               (k1_zfmisc_1 @ 
% 4.39/4.58                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 4.39/4.58          | (v5_pre_topc @ X5 @ X6 @ 
% 4.39/4.58             (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 4.39/4.58          | ~ (v5_pre_topc @ X5 @ X6 @ X4)
% 4.39/4.58          | ~ (m1_subset_1 @ X5 @ 
% 4.39/4.58               (k1_zfmisc_1 @ 
% 4.39/4.58                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ 
% 4.39/4.58                 (u1_struct_0 @ 
% 4.39/4.58                  (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4))))))
% 4.39/4.58          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ 
% 4.39/4.58               (u1_struct_0 @ 
% 4.39/4.58                (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4))))
% 4.39/4.58          | ~ (v1_funct_1 @ X5)
% 4.39/4.58          | ~ (l1_pre_topc @ X4)
% 4.39/4.58          | ~ (v2_pre_topc @ X4))),
% 4.39/4.58      inference('simplify', [status(thm)], ['35'])).
% 4.39/4.58  thf('37', plain,
% 4.39/4.58      ((![X0 : $i, X1 : $i]:
% 4.39/4.58          (~ (m1_subset_1 @ X1 @ 
% 4.39/4.58              (k1_zfmisc_1 @ 
% 4.39/4.58               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 4.39/4.58                (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 4.39/4.58           | ~ (v2_pre_topc @ sk_A)
% 4.39/4.58           | ~ (l1_pre_topc @ sk_A)
% 4.39/4.58           | ~ (v1_funct_1 @ X1)
% 4.39/4.58           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ 
% 4.39/4.58                (u1_struct_0 @ 
% 4.39/4.58                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 4.39/4.58           | ~ (v5_pre_topc @ X1 @ X0 @ sk_A)
% 4.39/4.58           | (v5_pre_topc @ X1 @ X0 @ 
% 4.39/4.58              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.39/4.58           | ~ (m1_subset_1 @ X1 @ 
% 4.39/4.58                (k1_zfmisc_1 @ 
% 4.39/4.58                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 4.39/4.58           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.39/4.58           | ~ (l1_pre_topc @ X0)
% 4.39/4.58           | ~ (v2_pre_topc @ X0)))
% 4.39/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.39/4.58      inference('sup-', [status(thm)], ['34', '36'])).
% 4.39/4.58  thf('38', plain,
% 4.39/4.58      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.39/4.58      inference('clc', [status(thm)], ['16', '17'])).
% 4.39/4.58  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('41', plain,
% 4.39/4.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 4.39/4.58          = (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.39/4.58      inference('sup-', [status(thm)], ['25', '33'])).
% 4.39/4.58  thf('42', plain,
% 4.39/4.58      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.39/4.58      inference('clc', [status(thm)], ['16', '17'])).
% 4.39/4.58  thf('43', plain,
% 4.39/4.58      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 4.39/4.58          = (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.39/4.58      inference('sup-', [status(thm)], ['25', '33'])).
% 4.39/4.58  thf('44', plain,
% 4.39/4.58      ((![X0 : $i, X1 : $i]:
% 4.39/4.58          (~ (m1_subset_1 @ X1 @ 
% 4.39/4.58              (k1_zfmisc_1 @ 
% 4.39/4.58               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 4.39/4.58           | ~ (v1_funct_1 @ X1)
% 4.39/4.58           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.39/4.58           | ~ (v5_pre_topc @ X1 @ X0 @ sk_A)
% 4.39/4.58           | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 4.39/4.58           | ~ (m1_subset_1 @ X1 @ 
% 4.39/4.58                (k1_zfmisc_1 @ 
% 4.39/4.58                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 4.39/4.58           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.39/4.58           | ~ (l1_pre_topc @ X0)
% 4.39/4.58           | ~ (v2_pre_topc @ X0)))
% 4.39/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.39/4.58      inference('demod', [status(thm)],
% 4.39/4.58                ['37', '38', '39', '40', '41', '42', '43'])).
% 4.39/4.58  thf('45', plain,
% 4.39/4.58      ((![X0 : $i, X1 : $i]:
% 4.39/4.58          (~ (v2_pre_topc @ X0)
% 4.39/4.58           | ~ (l1_pre_topc @ X0)
% 4.39/4.58           | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 4.39/4.58           | ~ (v5_pre_topc @ X1 @ X0 @ sk_A)
% 4.39/4.58           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.39/4.58           | ~ (v1_funct_1 @ X1)
% 4.39/4.58           | ~ (m1_subset_1 @ X1 @ 
% 4.39/4.58                (k1_zfmisc_1 @ 
% 4.39/4.58                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))))
% 4.39/4.58         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.39/4.58      inference('simplify', [status(thm)], ['44'])).
% 4.39/4.58  thf('46', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('47', plain,
% 4.39/4.58      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.58         (k6_tmap_1 @ sk_A @ sk_B))
% 4.39/4.58        | (v3_pre_topc @ sk_B @ sk_A))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('48', plain,
% 4.39/4.58      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.58         (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.58         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.58               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.39/4.58      inference('split', [status(esa)], ['47'])).
% 4.39/4.58  thf('49', plain,
% 4.39/4.58      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 4.39/4.58         (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.58         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.58               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.39/4.58      inference('sup+', [status(thm)], ['46', '48'])).
% 4.39/4.58  thf('50', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('51', plain,
% 4.39/4.58      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.39/4.58      inference('clc', [status(thm)], ['16', '17'])).
% 4.39/4.58  thf('52', plain,
% 4.39/4.58      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.58         (k1_zfmisc_1 @ 
% 4.39/4.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 4.39/4.58        | (v3_pre_topc @ sk_B @ sk_A))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('53', plain,
% 4.39/4.58      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.58         (k1_zfmisc_1 @ 
% 4.39/4.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 4.39/4.58         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.58               (k1_zfmisc_1 @ 
% 4.39/4.58                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.39/4.58      inference('split', [status(esa)], ['52'])).
% 4.39/4.58  thf('54', plain,
% 4.39/4.58      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.58         (k1_zfmisc_1 @ 
% 4.39/4.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 4.39/4.58         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.58               (k1_zfmisc_1 @ 
% 4.39/4.58                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.39/4.58      inference('sup+', [status(thm)], ['51', '53'])).
% 4.39/4.58  thf('55', plain,
% 4.39/4.58      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.39/4.58         (k1_zfmisc_1 @ 
% 4.39/4.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 4.39/4.58         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.58               (k1_zfmisc_1 @ 
% 4.39/4.58                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.39/4.58      inference('sup+', [status(thm)], ['50', '54'])).
% 4.39/4.58  thf('56', plain,
% 4.39/4.58      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.58           (k1_zfmisc_1 @ 
% 4.39/4.58            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 4.39/4.58        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.58             (k6_tmap_1 @ sk_A @ sk_B))
% 4.39/4.58        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.58        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 4.39/4.58        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('57', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('58', plain,
% 4.39/4.58      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.39/4.58      inference('clc', [status(thm)], ['16', '17'])).
% 4.39/4.58  thf('59', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('60', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('61', plain,
% 4.39/4.58      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.39/4.58      inference('clc', [status(thm)], ['16', '17'])).
% 4.39/4.58  thf('62', plain,
% 4.39/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('63', plain,
% 4.39/4.58      (![X26 : $i, X27 : $i]:
% 4.39/4.58         (~ (l1_pre_topc @ X26)
% 4.39/4.58          | ~ (v2_pre_topc @ X26)
% 4.39/4.58          | (v2_struct_0 @ X26)
% 4.39/4.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.39/4.58          | (v1_funct_2 @ (k7_tmap_1 @ X26 @ X27) @ (u1_struct_0 @ X26) @ 
% 4.39/4.58             (u1_struct_0 @ (k6_tmap_1 @ X26 @ X27))))),
% 4.39/4.58      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 4.39/4.58  thf('64', plain,
% 4.39/4.58      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.58         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.58        | (v2_struct_0 @ sk_A)
% 4.39/4.58        | ~ (v2_pre_topc @ sk_A)
% 4.39/4.58        | ~ (l1_pre_topc @ sk_A))),
% 4.39/4.58      inference('sup-', [status(thm)], ['62', '63'])).
% 4.39/4.58  thf('65', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('66', plain,
% 4.39/4.58      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.39/4.58      inference('clc', [status(thm)], ['16', '17'])).
% 4.39/4.58  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('69', plain,
% 4.39/4.58      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.39/4.58         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.39/4.58        | (v2_struct_0 @ sk_A))),
% 4.39/4.58      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 4.39/4.58  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('71', plain,
% 4.39/4.58      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.39/4.58        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 4.39/4.58      inference('clc', [status(thm)], ['69', '70'])).
% 4.39/4.58  thf('72', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('73', plain,
% 4.39/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('74', plain,
% 4.39/4.58      (![X26 : $i, X27 : $i]:
% 4.39/4.58         (~ (l1_pre_topc @ X26)
% 4.39/4.58          | ~ (v2_pre_topc @ X26)
% 4.39/4.58          | (v2_struct_0 @ X26)
% 4.39/4.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.39/4.58          | (v1_funct_1 @ (k7_tmap_1 @ X26 @ X27)))),
% 4.39/4.58      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 4.39/4.58  thf('75', plain,
% 4.39/4.58      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 4.39/4.58        | (v2_struct_0 @ sk_A)
% 4.39/4.58        | ~ (v2_pre_topc @ sk_A)
% 4.39/4.58        | ~ (l1_pre_topc @ sk_A))),
% 4.39/4.58      inference('sup-', [status(thm)], ['73', '74'])).
% 4.39/4.58  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('78', plain,
% 4.39/4.58      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 4.39/4.58      inference('demod', [status(thm)], ['75', '76', '77'])).
% 4.39/4.58  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf('80', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 4.39/4.58      inference('clc', [status(thm)], ['78', '79'])).
% 4.39/4.58  thf('81', plain,
% 4.39/4.58      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.58      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.58  thf('82', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.59      inference('demod', [status(thm)], ['80', '81'])).
% 4.39/4.59  thf('83', plain,
% 4.39/4.59      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.39/4.59           (k1_zfmisc_1 @ 
% 4.39/4.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 4.39/4.59        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 4.39/4.59             (k6_tmap_1 @ sk_A @ sk_B))
% 4.39/4.59        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.39/4.59      inference('demod', [status(thm)],
% 4.39/4.59                ['56', '57', '58', '59', '60', '61', '71', '72', '82'])).
% 4.39/4.59  thf('84', plain,
% 4.39/4.59      (((~ (v3_pre_topc @ sk_B @ sk_A)
% 4.39/4.59         | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 4.39/4.59              (k6_tmap_1 @ sk_A @ sk_B))))
% 4.39/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59               (k1_zfmisc_1 @ 
% 4.39/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.39/4.59      inference('sup-', [status(thm)], ['55', '83'])).
% 4.39/4.59  thf('85', plain,
% 4.39/4.59      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 4.39/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.59               (k6_tmap_1 @ sk_A @ sk_B))) & 
% 4.39/4.59             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59               (k1_zfmisc_1 @ 
% 4.39/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.39/4.59      inference('sup-', [status(thm)], ['49', '84'])).
% 4.39/4.59  thf('86', plain,
% 4.39/4.59      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.39/4.59        (k1_zfmisc_1 @ 
% 4.39/4.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 4.39/4.59      inference('clc', [status(thm)], ['21', '22'])).
% 4.39/4.59  thf('87', plain,
% 4.39/4.59      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.39/4.59      inference('clc', [status(thm)], ['8', '9'])).
% 4.39/4.59  thf('88', plain,
% 4.39/4.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.39/4.59      inference('clc', [status(thm)], ['16', '17'])).
% 4.39/4.59  thf('89', plain,
% 4.39/4.59      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59           (k1_zfmisc_1 @ 
% 4.39/4.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 4.39/4.59        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.59             (k6_tmap_1 @ sk_A @ sk_B))
% 4.39/4.59        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.59        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 4.39/4.59        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.39/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.59  thf('90', plain,
% 4.39/4.59      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59           (k1_zfmisc_1 @ 
% 4.39/4.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 4.39/4.59         <= (~
% 4.39/4.59             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59               (k1_zfmisc_1 @ 
% 4.39/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.39/4.59      inference('split', [status(esa)], ['89'])).
% 4.39/4.59  thf('91', plain,
% 4.39/4.59      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59           (k1_zfmisc_1 @ 
% 4.39/4.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 4.39/4.59         <= (~
% 4.39/4.59             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59               (k1_zfmisc_1 @ 
% 4.39/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.39/4.59      inference('sup-', [status(thm)], ['88', '90'])).
% 4.39/4.59  thf('92', plain,
% 4.39/4.59      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.39/4.59           (k1_zfmisc_1 @ 
% 4.39/4.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 4.39/4.59         <= (~
% 4.39/4.59             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59               (k1_zfmisc_1 @ 
% 4.39/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.39/4.59      inference('sup-', [status(thm)], ['87', '91'])).
% 4.39/4.59  thf('93', plain,
% 4.39/4.59      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59         (k1_zfmisc_1 @ 
% 4.39/4.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 4.39/4.59      inference('sup-', [status(thm)], ['86', '92'])).
% 4.39/4.59  thf('94', plain,
% 4.39/4.59      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.39/4.59         (k1_zfmisc_1 @ 
% 4.39/4.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.39/4.59           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 4.39/4.59      inference('sat_resolution*', [status(thm)], ['93'])).
% 4.39/4.59  thf('95', plain,
% 4.39/4.59      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 4.39/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.39/4.59      inference('simpl_trail', [status(thm)], ['85', '94'])).
% 4.39/4.59  thf('96', plain,
% 4.39/4.59      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.59         (k6_tmap_1 @ sk_A @ sk_B)))
% 4.39/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.39/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.39/4.59      inference('split', [status(esa)], ['47'])).
% 4.39/4.59  thf(t55_tops_2, axiom,
% 4.39/4.59    (![A:$i]:
% 4.39/4.59     ( ( l1_pre_topc @ A ) =>
% 4.39/4.59       ( ![B:$i]:
% 4.39/4.59         ( ( l1_pre_topc @ B ) =>
% 4.39/4.59           ( ![C:$i]:
% 4.39/4.59             ( ( ( m1_subset_1 @
% 4.39/4.59                   C @ 
% 4.39/4.59                   ( k1_zfmisc_1 @
% 4.39/4.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 4.39/4.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.43/4.59                 ( v1_funct_1 @ C ) ) =>
% 4.43/4.59               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 4.43/4.59                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.43/4.59                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.43/4.59                   ( ![D:$i]:
% 4.43/4.59                     ( ( m1_subset_1 @
% 4.43/4.59                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.43/4.59                       ( ( v3_pre_topc @ D @ B ) =>
% 4.43/4.59                         ( v3_pre_topc @
% 4.43/4.59                           ( k8_relset_1 @
% 4.43/4.59                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.43/4.59                           A ) ) ) ) ) ) ) ) ) ) ))).
% 4.43/4.59  thf(zf_stmt_1, axiom,
% 4.43/4.59    (![C:$i,B:$i,A:$i]:
% 4.43/4.59     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 4.43/4.59       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.43/4.59         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 4.43/4.59  thf('97', plain,
% 4.43/4.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 4.43/4.59         (~ (v5_pre_topc @ X17 @ X15 @ X16)
% 4.43/4.59          | (zip_tseitin_1 @ X18 @ X17 @ X16 @ X15)
% 4.43/4.59          | ~ (zip_tseitin_2 @ X17 @ X16 @ X15))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.43/4.59  thf('98', plain,
% 4.43/4.59      ((![X0 : $i]:
% 4.43/4.59          (~ (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59           | (zip_tseitin_1 @ X0 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['96', '97'])).
% 4.43/4.59  thf('99', plain,
% 4.43/4.59      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('clc', [status(thm)], ['8', '9'])).
% 4.43/4.59  thf('100', plain,
% 4.43/4.59      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('clc', [status(thm)], ['8', '9'])).
% 4.43/4.59  thf('101', plain,
% 4.43/4.59      ((![X0 : $i]:
% 4.43/4.59          (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['98', '99', '100'])).
% 4.43/4.59  thf(zf_stmt_2, axiom,
% 4.43/4.59    (![B:$i,A:$i]:
% 4.43/4.59     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 4.43/4.59         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.43/4.59       ( zip_tseitin_0 @ B @ A ) ))).
% 4.43/4.59  thf('102', plain,
% 4.43/4.59      (![X8 : $i, X9 : $i]:
% 4.43/4.59         ((zip_tseitin_0 @ X8 @ X9) | ((k2_struct_0 @ X8) = (k1_xboole_0)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.43/4.59  thf('103', plain,
% 4.43/4.59      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59         (k1_zfmisc_1 @ 
% 4.43/4.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('split', [status(esa)], ['52'])).
% 4.43/4.59  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 4.43/4.59  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 4.43/4.59  thf(zf_stmt_5, axiom,
% 4.43/4.59    (![D:$i,C:$i,B:$i,A:$i]:
% 4.43/4.59     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 4.43/4.59       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.43/4.59         ( ( v3_pre_topc @ D @ B ) =>
% 4.43/4.59           ( v3_pre_topc @
% 4.43/4.59             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.43/4.59             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 4.43/4.59  thf(zf_stmt_7, axiom,
% 4.43/4.59    (![A:$i]:
% 4.43/4.59     ( ( l1_pre_topc @ A ) =>
% 4.43/4.59       ( ![B:$i]:
% 4.43/4.59         ( ( l1_pre_topc @ B ) =>
% 4.43/4.59           ( ![C:$i]:
% 4.43/4.59             ( ( ( v1_funct_1 @ C ) & 
% 4.43/4.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.43/4.59                 ( m1_subset_1 @
% 4.43/4.59                   C @ 
% 4.43/4.59                   ( k1_zfmisc_1 @
% 4.43/4.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.43/4.59               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 4.43/4.59  thf('104', plain,
% 4.43/4.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.43/4.59         (~ (l1_pre_topc @ X19)
% 4.43/4.59          | ~ (zip_tseitin_0 @ X19 @ X20)
% 4.43/4.59          | (zip_tseitin_2 @ X21 @ X19 @ X20)
% 4.43/4.59          | ~ (m1_subset_1 @ X21 @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 4.43/4.59          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 4.43/4.59          | ~ (v1_funct_1 @ X21)
% 4.43/4.59          | ~ (l1_pre_topc @ X20))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_7])).
% 4.43/4.59  thf('105', plain,
% 4.43/4.59      (((~ (l1_pre_topc @ sk_A)
% 4.43/4.59         | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 4.43/4.59         | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59              (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 4.43/4.59         | (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59            (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59         | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['103', '104'])).
% 4.43/4.59  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('107', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 4.43/4.59      inference('clc', [status(thm)], ['78', '79'])).
% 4.43/4.59  thf('108', plain,
% 4.43/4.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['16', '17'])).
% 4.43/4.59  thf('109', plain,
% 4.43/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf(dt_k6_tmap_1, axiom,
% 4.43/4.59    (![A:$i,B:$i]:
% 4.43/4.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.43/4.59         ( l1_pre_topc @ A ) & 
% 4.43/4.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.43/4.59       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 4.43/4.59         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 4.43/4.59         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 4.43/4.59  thf('110', plain,
% 4.43/4.59      (![X24 : $i, X25 : $i]:
% 4.43/4.59         (~ (l1_pre_topc @ X24)
% 4.43/4.59          | ~ (v2_pre_topc @ X24)
% 4.43/4.59          | (v2_struct_0 @ X24)
% 4.43/4.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 4.43/4.59          | (l1_pre_topc @ (k6_tmap_1 @ X24 @ X25)))),
% 4.43/4.59      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 4.43/4.59  thf('111', plain,
% 4.43/4.59      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 4.43/4.59        | (v2_struct_0 @ sk_A)
% 4.43/4.59        | ~ (v2_pre_topc @ sk_A)
% 4.43/4.59        | ~ (l1_pre_topc @ sk_A))),
% 4.43/4.59      inference('sup-', [status(thm)], ['109', '110'])).
% 4.43/4.59  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('114', plain,
% 4.43/4.59      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 4.43/4.59      inference('demod', [status(thm)], ['111', '112', '113'])).
% 4.43/4.59  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('116', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 4.43/4.59      inference('clc', [status(thm)], ['114', '115'])).
% 4.43/4.59  thf('117', plain,
% 4.43/4.59      (((~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59            (u1_struct_0 @ sk_A))
% 4.43/4.59         | (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59            (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('demod', [status(thm)], ['105', '106', '107', '108', '116'])).
% 4.43/4.59  thf('118', plain,
% 4.43/4.59      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('clc', [status(thm)], ['8', '9'])).
% 4.43/4.59  thf('119', plain,
% 4.43/4.59      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['69', '70'])).
% 4.43/4.59  thf('120', plain,
% 4.43/4.59      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('clc', [status(thm)], ['8', '9'])).
% 4.43/4.59  thf('121', plain,
% 4.43/4.59      ((((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59          (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 4.43/4.59  thf('122', plain,
% 4.43/4.59      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59         (k1_zfmisc_1 @ 
% 4.43/4.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 4.43/4.59      inference('sat_resolution*', [status(thm)], ['93'])).
% 4.43/4.59  thf('123', plain,
% 4.43/4.59      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59        | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 4.43/4.59      inference('simpl_trail', [status(thm)], ['121', '122'])).
% 4.43/4.59  thf('124', plain,
% 4.43/4.59      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 4.43/4.59        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 4.43/4.59      inference('sup-', [status(thm)], ['102', '123'])).
% 4.43/4.59  thf(d3_struct_0, axiom,
% 4.43/4.59    (![A:$i]:
% 4.43/4.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.43/4.59  thf('125', plain,
% 4.43/4.59      (![X2 : $i]:
% 4.43/4.59         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 4.43/4.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.43/4.59  thf('126', plain,
% 4.43/4.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['16', '17'])).
% 4.43/4.59  thf('127', plain,
% 4.43/4.59      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 4.43/4.59        | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 4.43/4.59      inference('sup+', [status(thm)], ['125', '126'])).
% 4.43/4.59  thf('128', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 4.43/4.59      inference('clc', [status(thm)], ['114', '115'])).
% 4.43/4.59  thf(dt_l1_pre_topc, axiom,
% 4.43/4.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 4.43/4.59  thf('129', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 4.43/4.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.43/4.59  thf('130', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 4.43/4.59      inference('sup-', [status(thm)], ['128', '129'])).
% 4.43/4.59  thf('131', plain,
% 4.43/4.59      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('demod', [status(thm)], ['127', '130'])).
% 4.43/4.59  thf('132', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 4.43/4.59        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 4.43/4.59      inference('demod', [status(thm)], ['124', '131'])).
% 4.43/4.59  thf('133', plain,
% 4.43/4.59      ((![X0 : $i]:
% 4.43/4.59          (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['98', '99', '100'])).
% 4.43/4.59  thf('134', plain,
% 4.43/4.59      ((![X0 : $i]:
% 4.43/4.59          (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 4.43/4.59           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['132', '133'])).
% 4.43/4.59  thf('135', plain,
% 4.43/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('136', plain,
% 4.43/4.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['16', '17'])).
% 4.43/4.59  thf('137', plain,
% 4.43/4.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 4.43/4.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 4.43/4.59          | (v3_pre_topc @ 
% 4.43/4.59             (k8_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13 @ 
% 4.43/4.59              X10) @ 
% 4.43/4.59             X12)
% 4.43/4.59          | ~ (v3_pre_topc @ X10 @ X11)
% 4.43/4.59          | ~ (zip_tseitin_1 @ X10 @ X13 @ X11 @ X12))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.43/4.59  thf('138', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.43/4.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.43/4.59          | ~ (zip_tseitin_1 @ X0 @ X2 @ (k6_tmap_1 @ sk_A @ sk_B) @ X1)
% 4.43/4.59          | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 4.43/4.59          | (v3_pre_topc @ 
% 4.43/4.59             (k8_relset_1 @ (u1_struct_0 @ X1) @ 
% 4.43/4.59              (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ X2 @ X0) @ 
% 4.43/4.59             X1))),
% 4.43/4.59      inference('sup-', [status(thm)], ['136', '137'])).
% 4.43/4.59  thf('139', plain,
% 4.43/4.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['16', '17'])).
% 4.43/4.59  thf('140', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.43/4.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.43/4.59          | ~ (zip_tseitin_1 @ X0 @ X2 @ (k6_tmap_1 @ sk_A @ sk_B) @ X1)
% 4.43/4.59          | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 4.43/4.59          | (v3_pre_topc @ 
% 4.43/4.59             (k8_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_A) @ X2 @ X0) @ 
% 4.43/4.59             X1))),
% 4.43/4.59      inference('demod', [status(thm)], ['138', '139'])).
% 4.43/4.59  thf('141', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i]:
% 4.43/4.59         ((v3_pre_topc @ 
% 4.43/4.59           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 4.43/4.59           X0)
% 4.43/4.59          | ~ (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 4.43/4.59          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 4.43/4.59      inference('sup-', [status(thm)], ['135', '140'])).
% 4.43/4.59  thf('142', plain,
% 4.43/4.59      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['16', '17'])).
% 4.43/4.59  thf(t105_tmap_1, axiom,
% 4.43/4.59    (![A:$i]:
% 4.43/4.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.43/4.59       ( ![B:$i]:
% 4.43/4.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.43/4.59           ( ![C:$i]:
% 4.43/4.59             ( ( m1_subset_1 @
% 4.43/4.59                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 4.43/4.59               ( ( ( C ) = ( B ) ) =>
% 4.43/4.59                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 4.43/4.59  thf('143', plain,
% 4.43/4.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.43/4.59         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 4.43/4.59          | ((X32) != (X30))
% 4.43/4.59          | (v3_pre_topc @ X32 @ (k6_tmap_1 @ X31 @ X30))
% 4.43/4.59          | ~ (m1_subset_1 @ X32 @ 
% 4.43/4.59               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X31 @ X30))))
% 4.43/4.59          | ~ (l1_pre_topc @ X31)
% 4.43/4.59          | ~ (v2_pre_topc @ X31)
% 4.43/4.59          | (v2_struct_0 @ X31))),
% 4.43/4.59      inference('cnf', [status(esa)], [t105_tmap_1])).
% 4.43/4.59  thf('144', plain,
% 4.43/4.59      (![X30 : $i, X31 : $i]:
% 4.43/4.59         ((v2_struct_0 @ X31)
% 4.43/4.59          | ~ (v2_pre_topc @ X31)
% 4.43/4.59          | ~ (l1_pre_topc @ X31)
% 4.43/4.59          | ~ (m1_subset_1 @ X30 @ 
% 4.43/4.59               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X31 @ X30))))
% 4.43/4.59          | (v3_pre_topc @ X30 @ (k6_tmap_1 @ X31 @ X30))
% 4.43/4.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 4.43/4.59      inference('simplify', [status(thm)], ['143'])).
% 4.43/4.59  thf('145', plain,
% 4.43/4.59      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.43/4.59        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.43/4.59        | (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 4.43/4.59        | ~ (l1_pre_topc @ sk_A)
% 4.43/4.59        | ~ (v2_pre_topc @ sk_A)
% 4.43/4.59        | (v2_struct_0 @ sk_A))),
% 4.43/4.59      inference('sup-', [status(thm)], ['142', '144'])).
% 4.43/4.59  thf('146', plain,
% 4.43/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('147', plain,
% 4.43/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('150', plain,
% 4.43/4.59      (((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 4.43/4.59      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 4.43/4.59  thf('151', plain, (~ (v2_struct_0 @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('152', plain, ((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))),
% 4.43/4.59      inference('clc', [status(thm)], ['150', '151'])).
% 4.43/4.59  thf('153', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i]:
% 4.43/4.59         ((v3_pre_topc @ 
% 4.43/4.59           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 4.43/4.59           X0)
% 4.43/4.59          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 4.43/4.59      inference('demod', [status(thm)], ['141', '152'])).
% 4.43/4.59  thf('154', plain,
% 4.43/4.59      (((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 4.43/4.59         | (v3_pre_topc @ 
% 4.43/4.59            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 4.43/4.59            sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['134', '153'])).
% 4.43/4.59  thf('155', plain,
% 4.43/4.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf(t171_funct_2, axiom,
% 4.43/4.59    (![A:$i,B:$i]:
% 4.43/4.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.43/4.59       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 4.43/4.59  thf('156', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i]:
% 4.43/4.59         (((k8_relset_1 @ X1 @ X1 @ (k6_partfun1 @ X1) @ X0) = (X0))
% 4.43/4.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 4.43/4.59      inference('cnf', [status(esa)], [t171_funct_2])).
% 4.43/4.59  thf('157', plain,
% 4.43/4.59      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 4.43/4.59      inference('sup-', [status(thm)], ['155', '156'])).
% 4.43/4.59  thf('158', plain,
% 4.43/4.59      (((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v3_pre_topc @ sk_B @ sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['154', '157'])).
% 4.43/4.59  thf('159', plain,
% 4.43/4.59      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('simpl_trail', [status(thm)], ['85', '94'])).
% 4.43/4.59  thf('160', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('161', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('162', plain,
% 4.43/4.59      ((![X0 : $i]:
% 4.43/4.59          (~ (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ k1_xboole_0) @ 
% 4.43/4.59              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['101', '160', '161'])).
% 4.43/4.59  thf('163', plain,
% 4.43/4.59      (![X2 : $i]:
% 4.43/4.59         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 4.43/4.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.43/4.59  thf('164', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('165', plain,
% 4.43/4.59      (((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('sup+', [status(thm)], ['163', '164'])).
% 4.43/4.59  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('167', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 4.43/4.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.43/4.59  thf('168', plain, ((l1_struct_0 @ sk_A)),
% 4.43/4.59      inference('sup-', [status(thm)], ['166', '167'])).
% 4.43/4.59  thf('169', plain,
% 4.43/4.59      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['165', '168'])).
% 4.43/4.59  thf('170', plain,
% 4.43/4.59      (![X8 : $i, X9 : $i]:
% 4.43/4.59         ((zip_tseitin_0 @ X8 @ X9) | ((k2_struct_0 @ X9) != (k1_xboole_0)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.43/4.59  thf('171', plain,
% 4.43/4.59      ((![X0 : $i]:
% 4.43/4.59          (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ sk_A)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['169', '170'])).
% 4.43/4.59  thf('172', plain,
% 4.43/4.59      ((![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_A))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('simplify', [status(thm)], ['171'])).
% 4.43/4.59  thf('173', plain,
% 4.43/4.59      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 4.43/4.59        | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 4.43/4.59      inference('simpl_trail', [status(thm)], ['121', '122'])).
% 4.43/4.59  thf('174', plain,
% 4.43/4.59      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['172', '173'])).
% 4.43/4.59  thf('175', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('176', plain,
% 4.43/4.59      (((zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 4.43/4.59         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['174', '175'])).
% 4.43/4.59  thf('177', plain,
% 4.43/4.59      ((![X0 : $i]:
% 4.43/4.59          (zip_tseitin_1 @ X0 @ (k6_partfun1 @ k1_xboole_0) @ 
% 4.43/4.59           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['162', '176'])).
% 4.43/4.59  thf('178', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i]:
% 4.43/4.59         ((v3_pre_topc @ 
% 4.43/4.59           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 4.43/4.59           X0)
% 4.43/4.59          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 4.43/4.59      inference('demod', [status(thm)], ['141', '152'])).
% 4.43/4.59  thf('179', plain,
% 4.43/4.59      (((v3_pre_topc @ 
% 4.43/4.59         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59          (k6_partfun1 @ k1_xboole_0) @ sk_B) @ 
% 4.43/4.59         sk_A))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['177', '178'])).
% 4.43/4.59  thf('180', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('181', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('182', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('183', plain,
% 4.43/4.59      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 4.43/4.59      inference('sup-', [status(thm)], ['155', '156'])).
% 4.43/4.59  thf('184', plain,
% 4.43/4.59      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59          (k6_partfun1 @ k1_xboole_0) @ sk_B) = (sk_B)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('sup+', [status(thm)], ['182', '183'])).
% 4.43/4.59  thf('185', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('186', plain,
% 4.43/4.59      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('clc', [status(thm)], ['158', '159'])).
% 4.43/4.59  thf('187', plain,
% 4.43/4.59      ((((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 4.43/4.59          (k6_partfun1 @ k1_xboole_0) @ sk_B) = (sk_B)))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['184', '185', '186'])).
% 4.43/4.59  thf('188', plain,
% 4.43/4.59      (((v3_pre_topc @ sk_B @ sk_A))
% 4.43/4.59         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['179', '180', '181', '187'])).
% 4.43/4.59  thf('189', plain,
% 4.43/4.59      (~
% 4.43/4.59       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59         (k6_tmap_1 @ sk_A @ sk_B)))),
% 4.43/4.59      inference('demod', [status(thm)], ['95', '188'])).
% 4.43/4.59  thf('190', plain,
% 4.43/4.59      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 4.43/4.59       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59         (k6_tmap_1 @ sk_A @ sk_B)))),
% 4.43/4.59      inference('split', [status(esa)], ['47'])).
% 4.43/4.59  thf('191', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 4.43/4.59      inference('sat_resolution*', [status(thm)], ['189', '190'])).
% 4.43/4.59  thf('192', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i]:
% 4.43/4.59         (~ (v2_pre_topc @ X0)
% 4.43/4.59          | ~ (l1_pre_topc @ X0)
% 4.43/4.59          | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 4.43/4.59          | ~ (v5_pre_topc @ X1 @ X0 @ sk_A)
% 4.43/4.59          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.43/4.59          | ~ (v1_funct_1 @ X1)
% 4.43/4.59          | ~ (m1_subset_1 @ X1 @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 4.43/4.59      inference('simpl_trail', [status(thm)], ['45', '191'])).
% 4.43/4.59  thf('193', plain,
% 4.43/4.59      ((~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 4.43/4.59        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.43/4.59        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)
% 4.43/4.59        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 4.43/4.59           (k6_tmap_1 @ sk_A @ sk_B))
% 4.43/4.59        | ~ (l1_pre_topc @ sk_A)
% 4.43/4.59        | ~ (v2_pre_topc @ sk_A))),
% 4.43/4.59      inference('sup-', [status(thm)], ['23', '192'])).
% 4.43/4.59  thf('194', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('demod', [status(thm)], ['80', '81'])).
% 4.43/4.59  thf('195', plain,
% 4.43/4.59      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['69', '70'])).
% 4.43/4.59  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('197', plain, ((v2_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('198', plain,
% 4.43/4.59      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)
% 4.43/4.59        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 4.43/4.59           (k6_tmap_1 @ sk_A @ sk_B)))),
% 4.43/4.59      inference('demod', [status(thm)], ['193', '194', '195', '196', '197'])).
% 4.43/4.59  thf('199', plain,
% 4.43/4.59      ((~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59           (k6_tmap_1 @ sk_A @ sk_B)))
% 4.43/4.59         <= (~
% 4.43/4.59             ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('split', [status(esa)], ['89'])).
% 4.43/4.59  thf('200', plain,
% 4.43/4.59      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('clc', [status(thm)], ['8', '9'])).
% 4.43/4.59  thf('201', plain,
% 4.43/4.59      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 4.43/4.59           (k6_tmap_1 @ sk_A @ sk_B)))
% 4.43/4.59         <= (~
% 4.43/4.59             ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59               (k6_tmap_1 @ sk_A @ sk_B))))),
% 4.43/4.59      inference('demod', [status(thm)], ['199', '200'])).
% 4.43/4.59  thf('202', plain,
% 4.43/4.59      (~
% 4.43/4.59       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 4.43/4.59         (k6_tmap_1 @ sk_A @ sk_B)))),
% 4.43/4.59      inference('sat_resolution*', [status(thm)], ['189'])).
% 4.43/4.59  thf('203', plain,
% 4.43/4.59      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 4.43/4.59          (k6_tmap_1 @ sk_A @ sk_B))),
% 4.43/4.59      inference('simpl_trail', [status(thm)], ['201', '202'])).
% 4.43/4.59  thf('204', plain,
% 4.43/4.59      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)),
% 4.43/4.59      inference('clc', [status(thm)], ['198', '203'])).
% 4.43/4.59  thf('205', plain,
% 4.43/4.59      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59        (k1_zfmisc_1 @ 
% 4.43/4.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 4.43/4.59      inference('clc', [status(thm)], ['21', '22'])).
% 4.43/4.59  thf('206', plain,
% 4.43/4.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.43/4.59         (~ (l1_pre_topc @ X19)
% 4.43/4.59          | ~ (zip_tseitin_0 @ X19 @ X20)
% 4.43/4.59          | (zip_tseitin_2 @ X21 @ X19 @ X20)
% 4.43/4.59          | ~ (m1_subset_1 @ X21 @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 4.43/4.59          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 4.43/4.59          | ~ (v1_funct_1 @ X21)
% 4.43/4.59          | ~ (l1_pre_topc @ X20))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_7])).
% 4.43/4.59  thf('207', plain,
% 4.43/4.59      ((~ (l1_pre_topc @ sk_A)
% 4.43/4.59        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 4.43/4.59        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.43/4.59        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)
% 4.43/4.59        | ~ (zip_tseitin_0 @ sk_A @ sk_A)
% 4.43/4.59        | ~ (l1_pre_topc @ sk_A))),
% 4.43/4.59      inference('sup-', [status(thm)], ['205', '206'])).
% 4.43/4.59  thf('208', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('209', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('demod', [status(thm)], ['80', '81'])).
% 4.43/4.59  thf('210', plain,
% 4.43/4.59      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['69', '70'])).
% 4.43/4.59  thf('211', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('212', plain,
% 4.43/4.59      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)
% 4.43/4.59        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 4.43/4.59      inference('demod', [status(thm)], ['207', '208', '209', '210', '211'])).
% 4.43/4.59  thf('213', plain,
% 4.43/4.59      (![X8 : $i, X9 : $i]:
% 4.43/4.59         ((zip_tseitin_0 @ X8 @ X9) | ((k2_struct_0 @ X8) = (k1_xboole_0)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.43/4.59  thf('214', plain,
% 4.43/4.59      (![X2 : $i]:
% 4.43/4.59         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 4.43/4.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.43/4.59  thf('215', plain,
% 4.43/4.59      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59         (k1_zfmisc_1 @ 
% 4.43/4.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('sup+', [status(thm)], ['51', '53'])).
% 4.43/4.59  thf('216', plain,
% 4.43/4.59      ((((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59          (k1_zfmisc_1 @ 
% 4.43/4.59           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 4.43/4.59         | ~ (l1_struct_0 @ sk_A)))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('sup+', [status(thm)], ['214', '215'])).
% 4.43/4.59  thf('217', plain, ((l1_struct_0 @ sk_A)),
% 4.43/4.59      inference('sup-', [status(thm)], ['166', '167'])).
% 4.43/4.59  thf('218', plain,
% 4.43/4.59      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59         (k1_zfmisc_1 @ 
% 4.43/4.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('demod', [status(thm)], ['216', '217'])).
% 4.43/4.59  thf('219', plain,
% 4.43/4.59      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('clc', [status(thm)], ['8', '9'])).
% 4.43/4.59  thf('220', plain,
% 4.43/4.59      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59         (k1_zfmisc_1 @ 
% 4.43/4.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('demod', [status(thm)], ['218', '219'])).
% 4.43/4.59  thf('221', plain,
% 4.43/4.59      (![X2 : $i]:
% 4.43/4.59         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 4.43/4.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.43/4.59  thf('222', plain,
% 4.43/4.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.43/4.59         (~ (l1_pre_topc @ X19)
% 4.43/4.59          | ~ (zip_tseitin_0 @ X19 @ X20)
% 4.43/4.59          | (zip_tseitin_2 @ X21 @ X19 @ X20)
% 4.43/4.59          | ~ (m1_subset_1 @ X21 @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 4.43/4.59          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 4.43/4.59          | ~ (v1_funct_1 @ X21)
% 4.43/4.59          | ~ (l1_pre_topc @ X20))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_7])).
% 4.43/4.59  thf('223', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.43/4.59         (~ (m1_subset_1 @ X2 @ 
% 4.43/4.59             (k1_zfmisc_1 @ 
% 4.43/4.59              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 4.43/4.59          | ~ (l1_struct_0 @ X0)
% 4.43/4.59          | ~ (l1_pre_topc @ X1)
% 4.43/4.59          | ~ (v1_funct_1 @ X2)
% 4.43/4.59          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 4.43/4.59          | (zip_tseitin_2 @ X2 @ X0 @ X1)
% 4.43/4.59          | ~ (zip_tseitin_0 @ X0 @ X1)
% 4.43/4.59          | ~ (l1_pre_topc @ X0))),
% 4.43/4.59      inference('sup-', [status(thm)], ['221', '222'])).
% 4.43/4.59  thf('224', plain,
% 4.43/4.59      (((~ (l1_pre_topc @ sk_A)
% 4.43/4.59         | ~ (zip_tseitin_0 @ sk_A @ sk_A)
% 4.43/4.59         | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)
% 4.43/4.59         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.43/4.59         | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 4.43/4.59         | ~ (l1_pre_topc @ sk_A)
% 4.43/4.59         | ~ (l1_struct_0 @ sk_A)))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['220', '223'])).
% 4.43/4.59  thf('225', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('226', plain,
% 4.43/4.59      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 4.43/4.59        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 4.43/4.59      inference('clc', [status(thm)], ['69', '70'])).
% 4.43/4.59  thf('227', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 4.43/4.59      inference('demod', [status(thm)], ['80', '81'])).
% 4.43/4.59  thf('228', plain, ((l1_pre_topc @ sk_A)),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.43/4.59  thf('229', plain, ((l1_struct_0 @ sk_A)),
% 4.43/4.59      inference('sup-', [status(thm)], ['166', '167'])).
% 4.43/4.59  thf('230', plain,
% 4.43/4.59      (((~ (zip_tseitin_0 @ sk_A @ sk_A)
% 4.43/4.59         | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('demod', [status(thm)],
% 4.43/4.59                ['224', '225', '226', '227', '228', '229'])).
% 4.43/4.59  thf('231', plain,
% 4.43/4.59      (((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 4.43/4.59         | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['213', '230'])).
% 4.43/4.59  thf('232', plain,
% 4.43/4.59      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 4.43/4.59         ((zip_tseitin_1 @ X10 @ X13 @ X11 @ X14)
% 4.43/4.59          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.43/4.59  thf('233', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i]:
% 4.43/4.59         (((k8_relset_1 @ X1 @ X1 @ (k6_partfun1 @ X1) @ X0) = (X0))
% 4.43/4.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 4.43/4.59      inference('cnf', [status(esa)], [t171_funct_2])).
% 4.43/4.59  thf('234', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.43/4.59         ((zip_tseitin_1 @ X1 @ X3 @ X0 @ X2)
% 4.43/4.59          | ((k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 4.43/4.59              (k6_partfun1 @ (u1_struct_0 @ X0)) @ X1) = (X1)))),
% 4.43/4.59      inference('sup-', [status(thm)], ['232', '233'])).
% 4.43/4.59  thf('235', plain,
% 4.43/4.59      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 4.43/4.59         ((zip_tseitin_1 @ X10 @ X13 @ X11 @ X14)
% 4.43/4.59          | ~ (v3_pre_topc @ 
% 4.43/4.59               (k8_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11) @ 
% 4.43/4.59                X13 @ X10) @ 
% 4.43/4.59               X14))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.43/4.59  thf('236', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.43/4.59         (~ (v3_pre_topc @ X0 @ X1)
% 4.43/4.59          | (zip_tseitin_1 @ X0 @ X3 @ X1 @ X2)
% 4.43/4.59          | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ X1)) @ X1 @ X1))),
% 4.43/4.59      inference('sup-', [status(thm)], ['234', '235'])).
% 4.43/4.59  thf('237', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i]:
% 4.43/4.59         (~ (v3_pre_topc @ X1 @ X0)
% 4.43/4.59          | (zip_tseitin_1 @ X1 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 4.43/4.59      inference('condensation', [status(thm)], ['236'])).
% 4.43/4.59  thf('238', plain,
% 4.43/4.59      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 4.43/4.59         ((zip_tseitin_1 @ X10 @ X13 @ X11 @ X14) | (v3_pre_topc @ X10 @ X11))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.43/4.59  thf('239', plain,
% 4.43/4.59      (![X0 : $i, X1 : $i]:
% 4.43/4.59         (zip_tseitin_1 @ X1 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)),
% 4.43/4.59      inference('clc', [status(thm)], ['237', '238'])).
% 4.43/4.59  thf('240', plain,
% 4.43/4.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.43/4.59         (~ (zip_tseitin_1 @ (sk_D @ X15 @ X16 @ X17) @ X17 @ X16 @ X15)
% 4.43/4.59          | (v5_pre_topc @ X17 @ X15 @ X16)
% 4.43/4.59          | ~ (zip_tseitin_2 @ X17 @ X16 @ X15))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.43/4.59  thf('241', plain,
% 4.43/4.59      (![X0 : $i]:
% 4.43/4.59         (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)
% 4.43/4.59          | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 4.43/4.59      inference('sup-', [status(thm)], ['239', '240'])).
% 4.43/4.59  thf('242', plain,
% 4.43/4.59      (((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 4.43/4.59         | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)))
% 4.43/4.59         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59               (k1_zfmisc_1 @ 
% 4.43/4.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 4.43/4.59      inference('sup-', [status(thm)], ['231', '241'])).
% 4.43/4.59  thf('243', plain,
% 4.43/4.59      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 4.43/4.59         (k1_zfmisc_1 @ 
% 4.43/4.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.43/4.59           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 4.43/4.59      inference('sat_resolution*', [status(thm)], ['93'])).
% 4.43/4.59  thf('244', plain,
% 4.43/4.59      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 4.43/4.59        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A))),
% 4.43/4.59      inference('simpl_trail', [status(thm)], ['242', '243'])).
% 4.43/4.59  thf('245', plain,
% 4.43/4.59      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)),
% 4.43/4.59      inference('clc', [status(thm)], ['198', '203'])).
% 4.43/4.59  thf('246', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 4.43/4.59      inference('sup-', [status(thm)], ['244', '245'])).
% 4.43/4.59  thf('247', plain,
% 4.43/4.59      (![X8 : $i, X9 : $i]:
% 4.43/4.59         ((zip_tseitin_0 @ X8 @ X9) | ((k2_struct_0 @ X9) != (k1_xboole_0)))),
% 4.43/4.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.43/4.59  thf('248', plain,
% 4.43/4.59      (![X0 : $i]:
% 4.43/4.59         (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ sk_A))),
% 4.43/4.59      inference('sup-', [status(thm)], ['246', '247'])).
% 4.43/4.59  thf('249', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_A)),
% 4.43/4.59      inference('simplify', [status(thm)], ['248'])).
% 4.43/4.59  thf('250', plain,
% 4.43/4.59      ((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)),
% 4.43/4.59      inference('demod', [status(thm)], ['212', '249'])).
% 4.43/4.59  thf('251', plain,
% 4.43/4.59      (![X0 : $i]:
% 4.43/4.59         (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)
% 4.43/4.59          | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 4.43/4.59      inference('sup-', [status(thm)], ['239', '240'])).
% 4.43/4.59  thf('252', plain,
% 4.43/4.59      ((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ sk_A)),
% 4.43/4.59      inference('sup-', [status(thm)], ['250', '251'])).
% 4.43/4.59  thf('253', plain, ($false), inference('demod', [status(thm)], ['204', '252'])).
% 4.43/4.59  
% 4.43/4.59  % SZS output end Refutation
% 4.43/4.59  
% 4.43/4.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
