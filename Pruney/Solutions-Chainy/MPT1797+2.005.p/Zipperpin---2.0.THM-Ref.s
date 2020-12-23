%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vZy0lcRHeV

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:53 EST 2020

% Result     : Theorem 8.64s
% Output     : Refutation 8.75s
% Verified   : 
% Statistics : Number of formulae       :  360 (272684 expanded)
%              Number of leaves         :   47 (77302 expanded)
%              Depth                    :   38
%              Number of atoms          : 4287 (7309248 expanded)
%              Number of equality atoms :  130 (64244 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X32 @ X31 ) )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

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
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
       => ( ( v3_pre_topc @ D @ B )
         => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X10 @ X13 @ X11 @ X14 )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relset_1 @ X1 @ X1 @ ( k6_partfun1 @ X1 ) @ X0 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X0 @ X2 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X10 @ X13 @ X11 @ X14 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) @ X13 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X1 @ X2 )
      | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ X1 ) ) @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X10 @ X13 @ X11 @ X14 )
      | ( v3_pre_topc @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ X1 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v5_pre_topc @ C @ A @ B )
      <=> ! [D: $i] :
            ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X15 @ X16 @ X17 ) @ X17 @ X16 @ X15 )
      | ( v5_pre_topc @ X17 @ X15 @ X16 )
      | ~ ( zip_tseitin_2 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 )
      | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('21',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ X27 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k7_tmap_1 @ X23 @ X22 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ sk_B )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ sk_B )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( ( k2_struct_0 @ B )
          = k1_xboole_0 )
       => ( ( k2_struct_0 @ A )
          = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( ( k2_struct_0 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('46',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

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

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('51',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['48','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('61',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['44','62'])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('66',plain,
    ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('68',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['63','70'])).

thf('72',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('77',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('85',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('92',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','82','92'])).

thf('94',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('95',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('97',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X37 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X37 ) @ ( u1_pre_topc @ X37 ) )
        = ( k6_tmap_1 @ X37 @ X36 ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

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

thf('109',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v5_pre_topc @ X5 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) @ X4 )
      | ( v5_pre_topc @ X7 @ X6 @ X4 )
      | ( X7 != X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('110',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( v5_pre_topc @ X5 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
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
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('114',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('121',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('122',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('123',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('124',plain,(
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
    inference(demod,[status(thm)],['111','119','120','121','122','123'])).

thf('125',plain,
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
    inference('sup-',[status(thm)],['107','124'])).

thf('126',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','106'])).

thf('130',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','106'])).

thf('131',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v5_pre_topc @ X0 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v5_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130','131'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( v5_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ( v5_pre_topc @ X0 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('135',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['135'])).

thf('137',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','136'])).

thf('138',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('139',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['140'])).

thf('142',plain,
    ( ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['139','141'])).

thf('143',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('144',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['138','144'])).

thf('146',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('147',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('150',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('151',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('152',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('153',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('154',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('155',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('156',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('157',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153','154','155','156'])).

thf('158',plain,
    ( ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','157'])).

thf('159',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','158'])).

thf('160',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('161',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('162',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('163',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['163'])).

thf('165',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['162','164'])).

thf('166',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['161','165'])).

thf('167',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['167'])).

thf('169',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['159','168'])).

thf('170',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['135'])).

thf('171',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( v5_pre_topc @ X17 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X18 @ X17 @ X16 @ X15 )
      | ~ ( zip_tseitin_2 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('172',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('174',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('175',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( ( k2_struct_0 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('177',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['140'])).

thf('178',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('179',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('182',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('183',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('184',plain,
    ( ( ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['179','180','181','182','183'])).

thf('185',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('186',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('187',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('188',plain,
    ( ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['167'])).

thf('190',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['176','190'])).

thf('192',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('193',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('195',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ sk_A )
          = k1_xboole_0 )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('198',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X13 @ X10 ) @ X12 )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( zip_tseitin_1 @ X10 @ X13 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['196','201'])).

thf('203',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

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

thf('204',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( X35 != X33 )
      | ( v3_pre_topc @ X35 @ ( k6_tmap_1 @ X34 @ X33 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X34 @ X33 ) ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('205',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X34 @ X33 ) ) ) )
      | ( v3_pre_topc @ X33 @ ( k6_tmap_1 @ X34 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['203','205'])).

thf('207',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207','208','209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['202','213'])).

thf('215',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','214'])).

thf('216',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relset_1 @ X1 @ X1 @ ( k6_partfun1 @ X1 ) @ X0 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('218',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['215','218'])).

thf('220',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['159','168'])).

thf('221',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('223',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','221','222'])).

thf('224',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('225',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('226',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('228',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( ( k2_struct_0 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('230',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( zip_tseitin_0 @ X0 @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ X0 @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['188','189'])).

thf('233',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('235',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['223','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['202','213'])).

thf('238',plain,
    ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('240',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('241',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('242',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['216','217'])).

thf('243',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B )
      = sk_B )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('245',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('246',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B )
      = sk_B )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['238','239','240','246'])).

thf('248',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','247'])).

thf('249',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['135'])).

thf('250',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v5_pre_topc @ X0 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['133','250'])).

thf('252',plain,
    ( ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','251'])).

thf('253',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('254',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('255',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,
    ( ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['163'])).

thf('257',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('258',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['248'])).

thf('260',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['255','260'])).

thf('262',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('263',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','262'])).

thf('264',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('265',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('266',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['264','265'])).

thf('267',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('268',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['263','268'])).

thf('270',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['255','260'])).

thf('271',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('272',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['269','272'])).

thf('274',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('275',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('276',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('277',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('278',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['274','275','276','277'])).

thf('279',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('280',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('281',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('282',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ( zip_tseitin_2 @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('284',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('285',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['279','285'])).

thf('287',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('288',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['286','287','288'])).

thf('290',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('291',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('292',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('293',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( ( k2_struct_0 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('294',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
       != k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('296',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('297',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('299',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['289','290','291','297','298','299'])).

thf('301',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['278','300'])).

thf('302',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('303',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('304',plain,(
    v1_funct_1 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['302','303'])).

thf('305',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('306',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('307',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('308',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','261'])).

thf('309',plain,(
    v1_funct_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['305','306','307','308'])).

thf('310',plain,(
    zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['301','304','309'])).

thf('311',plain,(
    $false ),
    inference(demod,[status(thm)],['273','310'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vZy0lcRHeV
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.64/8.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.64/8.91  % Solved by: fo/fo7.sh
% 8.64/8.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.64/8.91  % done 3597 iterations in 8.427s
% 8.64/8.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.64/8.91  % SZS output start Refutation
% 8.64/8.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.64/8.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 8.64/8.91  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 8.64/8.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.64/8.91  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 8.64/8.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.64/8.91  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 8.64/8.91  thf(sk_B_type, type, sk_B: $i).
% 8.64/8.91  thf(sk_A_type, type, sk_A: $i).
% 8.64/8.91  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 8.64/8.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 8.64/8.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 8.64/8.91  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 8.64/8.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.64/8.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.64/8.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.64/8.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.64/8.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.64/8.91  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 8.64/8.91  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 8.64/8.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.64/8.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.64/8.91  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 8.64/8.91  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 8.64/8.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 8.64/8.91  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 8.64/8.91  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 8.64/8.91  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 8.64/8.91  thf(d3_struct_0, axiom,
% 8.64/8.91    (![A:$i]:
% 8.64/8.91     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 8.64/8.91  thf('0', plain,
% 8.64/8.91      (![X2 : $i]:
% 8.64/8.91         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 8.64/8.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.64/8.91  thf(t113_tmap_1, conjecture,
% 8.64/8.91    (![A:$i]:
% 8.64/8.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.64/8.91       ( ![B:$i]:
% 8.64/8.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.64/8.91           ( ( v3_pre_topc @ B @ A ) <=>
% 8.64/8.91             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 8.64/8.91               ( v1_funct_2 @
% 8.64/8.91                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 8.64/8.91                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 8.64/8.91               ( v5_pre_topc @
% 8.64/8.91                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 8.64/8.91               ( m1_subset_1 @
% 8.64/8.91                 ( k7_tmap_1 @ A @ B ) @ 
% 8.64/8.91                 ( k1_zfmisc_1 @
% 8.64/8.91                   ( k2_zfmisc_1 @
% 8.64/8.91                     ( u1_struct_0 @ A ) @ 
% 8.64/8.91                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 8.64/8.91  thf(zf_stmt_0, negated_conjecture,
% 8.64/8.91    (~( ![A:$i]:
% 8.64/8.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 8.64/8.91            ( l1_pre_topc @ A ) ) =>
% 8.64/8.91          ( ![B:$i]:
% 8.64/8.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.64/8.91              ( ( v3_pre_topc @ B @ A ) <=>
% 8.64/8.91                ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 8.64/8.91                  ( v1_funct_2 @
% 8.64/8.91                    ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 8.64/8.91                    ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 8.64/8.91                  ( v5_pre_topc @
% 8.64/8.91                    ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 8.64/8.91                  ( m1_subset_1 @
% 8.64/8.91                    ( k7_tmap_1 @ A @ B ) @ 
% 8.64/8.91                    ( k1_zfmisc_1 @
% 8.64/8.91                      ( k2_zfmisc_1 @
% 8.64/8.91                        ( u1_struct_0 @ A ) @ 
% 8.64/8.91                        ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 8.64/8.91    inference('cnf.neg', [status(esa)], [t113_tmap_1])).
% 8.64/8.91  thf('1', plain,
% 8.64/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf(t104_tmap_1, axiom,
% 8.64/8.91    (![A:$i]:
% 8.64/8.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.64/8.91       ( ![B:$i]:
% 8.64/8.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.64/8.91           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 8.64/8.91             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 8.64/8.91  thf('2', plain,
% 8.64/8.91      (![X31 : $i, X32 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 8.64/8.91          | ((u1_struct_0 @ (k6_tmap_1 @ X32 @ X31)) = (u1_struct_0 @ X32))
% 8.64/8.91          | ~ (l1_pre_topc @ X32)
% 8.64/8.91          | ~ (v2_pre_topc @ X32)
% 8.64/8.91          | (v2_struct_0 @ X32))),
% 8.64/8.91      inference('cnf', [status(esa)], [t104_tmap_1])).
% 8.64/8.91  thf('3', plain,
% 8.64/8.91      (((v2_struct_0 @ sk_A)
% 8.64/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91        | ~ (l1_pre_topc @ sk_A)
% 8.64/8.91        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['1', '2'])).
% 8.64/8.91  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('6', plain,
% 8.64/8.91      (((v2_struct_0 @ sk_A)
% 8.64/8.91        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('demod', [status(thm)], ['3', '4', '5'])).
% 8.64/8.91  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('8', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf(t55_tops_2, axiom,
% 8.64/8.91    (![A:$i]:
% 8.64/8.91     ( ( l1_pre_topc @ A ) =>
% 8.64/8.91       ( ![B:$i]:
% 8.64/8.91         ( ( l1_pre_topc @ B ) =>
% 8.64/8.91           ( ![C:$i]:
% 8.64/8.91             ( ( ( m1_subset_1 @
% 8.64/8.91                   C @ 
% 8.64/8.91                   ( k1_zfmisc_1 @
% 8.64/8.91                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.64/8.91                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.64/8.91                 ( v1_funct_1 @ C ) ) =>
% 8.64/8.91               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 8.64/8.91                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 8.64/8.91                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 8.64/8.91                   ( ![D:$i]:
% 8.64/8.91                     ( ( m1_subset_1 @
% 8.64/8.91                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 8.64/8.91                       ( ( v3_pre_topc @ D @ B ) =>
% 8.64/8.91                         ( v3_pre_topc @
% 8.64/8.91                           ( k8_relset_1 @
% 8.64/8.91                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 8.64/8.91                           A ) ) ) ) ) ) ) ) ) ) ))).
% 8.64/8.91  thf(zf_stmt_1, axiom,
% 8.64/8.91    (![D:$i,C:$i,B:$i,A:$i]:
% 8.64/8.91     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 8.64/8.91       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 8.64/8.91         ( ( v3_pre_topc @ D @ B ) =>
% 8.64/8.91           ( v3_pre_topc @
% 8.64/8.91             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 8.64/8.91             A ) ) ) ))).
% 8.64/8.91  thf('9', plain,
% 8.64/8.91      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 8.64/8.91         ((zip_tseitin_1 @ X10 @ X13 @ X11 @ X14)
% 8.64/8.91          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.64/8.91  thf(t171_funct_2, axiom,
% 8.64/8.91    (![A:$i,B:$i]:
% 8.64/8.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.64/8.91       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 8.64/8.91  thf('10', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i]:
% 8.64/8.91         (((k8_relset_1 @ X1 @ X1 @ (k6_partfun1 @ X1) @ X0) = (X0))
% 8.64/8.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 8.64/8.91      inference('cnf', [status(esa)], [t171_funct_2])).
% 8.64/8.91  thf('11', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.64/8.91         ((zip_tseitin_1 @ X1 @ X3 @ X0 @ X2)
% 8.64/8.91          | ((k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 8.64/8.91              (k6_partfun1 @ (u1_struct_0 @ X0)) @ X1) = (X1)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['9', '10'])).
% 8.64/8.91  thf('12', plain,
% 8.64/8.91      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 8.64/8.91         ((zip_tseitin_1 @ X10 @ X13 @ X11 @ X14)
% 8.64/8.91          | ~ (v3_pre_topc @ 
% 8.64/8.91               (k8_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11) @ 
% 8.64/8.91                X13 @ X10) @ 
% 8.64/8.91               X14))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.64/8.91  thf('13', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.64/8.91         (~ (v3_pre_topc @ X0 @ X1)
% 8.64/8.91          | (zip_tseitin_1 @ X0 @ X3 @ X1 @ X2)
% 8.64/8.91          | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ X1)) @ X1 @ X1))),
% 8.64/8.91      inference('sup-', [status(thm)], ['11', '12'])).
% 8.64/8.91  thf('14', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i]:
% 8.64/8.91         (~ (v3_pre_topc @ X1 @ X0)
% 8.64/8.91          | (zip_tseitin_1 @ X1 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 8.64/8.91      inference('condensation', [status(thm)], ['13'])).
% 8.64/8.91  thf('15', plain,
% 8.64/8.91      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 8.64/8.91         ((zip_tseitin_1 @ X10 @ X13 @ X11 @ X14) | (v3_pre_topc @ X10 @ X11))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.64/8.91  thf('16', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i]:
% 8.64/8.91         (zip_tseitin_1 @ X1 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)),
% 8.64/8.91      inference('clc', [status(thm)], ['14', '15'])).
% 8.64/8.91  thf(zf_stmt_2, axiom,
% 8.64/8.91    (![C:$i,B:$i,A:$i]:
% 8.64/8.91     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 8.64/8.91       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 8.64/8.91         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 8.64/8.91  thf('17', plain,
% 8.64/8.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 8.64/8.91         (~ (zip_tseitin_1 @ (sk_D @ X15 @ X16 @ X17) @ X17 @ X16 @ X15)
% 8.64/8.91          | (v5_pre_topc @ X17 @ X15 @ X16)
% 8.64/8.91          | ~ (zip_tseitin_2 @ X17 @ X16 @ X15))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 8.64/8.91  thf('18', plain,
% 8.64/8.91      (![X0 : $i]:
% 8.64/8.91         (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)
% 8.64/8.91          | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 8.64/8.91      inference('sup-', [status(thm)], ['16', '17'])).
% 8.64/8.91  thf('19', plain,
% 8.64/8.91      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | (v5_pre_topc @ 
% 8.64/8.91           (k6_partfun1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['8', '18'])).
% 8.64/8.91  thf('20', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('21', plain,
% 8.64/8.91      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.64/8.91      inference('demod', [status(thm)], ['19', '20'])).
% 8.64/8.91  thf('22', plain,
% 8.64/8.91      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | ~ (l1_struct_0 @ sk_A)
% 8.64/8.91        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['0', '21'])).
% 8.64/8.91  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf(dt_l1_pre_topc, axiom,
% 8.64/8.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 8.64/8.91  thf('24', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 8.64/8.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.64/8.91  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 8.64/8.91      inference('sup-', [status(thm)], ['23', '24'])).
% 8.64/8.91  thf('26', plain,
% 8.64/8.91      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.64/8.91      inference('demod', [status(thm)], ['22', '25'])).
% 8.64/8.91  thf('27', plain,
% 8.64/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf(dt_k7_tmap_1, axiom,
% 8.64/8.91    (![A:$i,B:$i]:
% 8.64/8.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 8.64/8.91         ( l1_pre_topc @ A ) & 
% 8.64/8.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.64/8.91       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 8.64/8.91         ( v1_funct_2 @
% 8.64/8.91           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 8.64/8.91           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 8.64/8.91         ( m1_subset_1 @
% 8.64/8.91           ( k7_tmap_1 @ A @ B ) @ 
% 8.64/8.91           ( k1_zfmisc_1 @
% 8.64/8.91             ( k2_zfmisc_1 @
% 8.64/8.91               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 8.64/8.91  thf('28', plain,
% 8.64/8.91      (![X26 : $i, X27 : $i]:
% 8.64/8.91         (~ (l1_pre_topc @ X26)
% 8.64/8.91          | ~ (v2_pre_topc @ X26)
% 8.64/8.91          | (v2_struct_0 @ X26)
% 8.64/8.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 8.64/8.91          | (m1_subset_1 @ (k7_tmap_1 @ X26 @ X27) @ 
% 8.64/8.91             (k1_zfmisc_1 @ 
% 8.64/8.91              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ 
% 8.64/8.91               (u1_struct_0 @ (k6_tmap_1 @ X26 @ X27))))))),
% 8.64/8.91      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 8.64/8.91  thf('29', plain,
% 8.64/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91         (k1_zfmisc_1 @ 
% 8.64/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.64/8.91           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 8.64/8.91        | (v2_struct_0 @ sk_A)
% 8.64/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91        | ~ (l1_pre_topc @ sk_A))),
% 8.64/8.91      inference('sup-', [status(thm)], ['27', '28'])).
% 8.64/8.91  thf('30', plain,
% 8.64/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf(d10_tmap_1, axiom,
% 8.64/8.91    (![A:$i]:
% 8.64/8.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.64/8.91       ( ![B:$i]:
% 8.64/8.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.64/8.91           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 8.64/8.91  thf('31', plain,
% 8.64/8.91      (![X22 : $i, X23 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 8.64/8.91          | ((k7_tmap_1 @ X23 @ X22) = (k6_partfun1 @ (u1_struct_0 @ X23)))
% 8.64/8.91          | ~ (l1_pre_topc @ X23)
% 8.64/8.91          | ~ (v2_pre_topc @ X23)
% 8.64/8.91          | (v2_struct_0 @ X23))),
% 8.64/8.91      inference('cnf', [status(esa)], [d10_tmap_1])).
% 8.64/8.91  thf('32', plain,
% 8.64/8.91      (((v2_struct_0 @ sk_A)
% 8.64/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91        | ~ (l1_pre_topc @ sk_A)
% 8.64/8.91        | ((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 8.64/8.91      inference('sup-', [status(thm)], ['30', '31'])).
% 8.64/8.91  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('35', plain,
% 8.64/8.91      (((v2_struct_0 @ sk_A)
% 8.64/8.91        | ((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 8.64/8.91      inference('demod', [status(thm)], ['32', '33', '34'])).
% 8.64/8.91  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('37', plain,
% 8.64/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.64/8.91  thf('38', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('41', plain,
% 8.64/8.91      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91         (k1_zfmisc_1 @ 
% 8.64/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.64/8.91        | (v2_struct_0 @ sk_A))),
% 8.64/8.91      inference('demod', [status(thm)], ['29', '37', '38', '39', '40'])).
% 8.64/8.91  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('43', plain,
% 8.64/8.91      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91        (k1_zfmisc_1 @ 
% 8.64/8.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 8.64/8.91      inference('clc', [status(thm)], ['41', '42'])).
% 8.64/8.91  thf(zf_stmt_3, axiom,
% 8.64/8.91    (![B:$i,A:$i]:
% 8.64/8.91     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 8.64/8.91         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 8.64/8.91       ( zip_tseitin_0 @ B @ A ) ))).
% 8.64/8.91  thf('44', plain,
% 8.64/8.91      (![X8 : $i, X9 : $i]:
% 8.64/8.91         ((zip_tseitin_0 @ X8 @ X9) | ((k2_struct_0 @ X8) = (k1_xboole_0)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.64/8.91  thf('45', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('46', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 8.64/8.91  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 8.64/8.91  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 8.64/8.91  thf(zf_stmt_7, axiom,
% 8.64/8.91    (![A:$i]:
% 8.64/8.91     ( ( l1_pre_topc @ A ) =>
% 8.64/8.91       ( ![B:$i]:
% 8.64/8.91         ( ( l1_pre_topc @ B ) =>
% 8.64/8.91           ( ![C:$i]:
% 8.64/8.91             ( ( ( v1_funct_1 @ C ) & 
% 8.64/8.91                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.64/8.91                 ( m1_subset_1 @
% 8.64/8.91                   C @ 
% 8.64/8.91                   ( k1_zfmisc_1 @
% 8.64/8.91                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.64/8.91               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 8.64/8.91  thf('47', plain,
% 8.64/8.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.64/8.91         (~ (l1_pre_topc @ X19)
% 8.64/8.91          | ~ (zip_tseitin_0 @ X19 @ X20)
% 8.64/8.91          | (zip_tseitin_2 @ X21 @ X19 @ X20)
% 8.64/8.91          | ~ (m1_subset_1 @ X21 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 8.64/8.91          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 8.64/8.91          | ~ (v1_funct_1 @ X21)
% 8.64/8.91          | ~ (l1_pre_topc @ X20))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 8.64/8.91  thf('48', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X1 @ 
% 8.64/8.91             (k1_zfmisc_1 @ 
% 8.64/8.91              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 8.64/8.91          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (v1_funct_1 @ X1)
% 8.64/8.91          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 8.64/8.91               (u1_struct_0 @ X0))
% 8.64/8.91          | (zip_tseitin_2 @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (l1_pre_topc @ X0))),
% 8.64/8.91      inference('sup-', [status(thm)], ['46', '47'])).
% 8.64/8.91  thf('49', plain,
% 8.64/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf(dt_k6_tmap_1, axiom,
% 8.64/8.91    (![A:$i,B:$i]:
% 8.64/8.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 8.64/8.91         ( l1_pre_topc @ A ) & 
% 8.64/8.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.64/8.91       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 8.64/8.91         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 8.64/8.91         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 8.64/8.91  thf('50', plain,
% 8.64/8.91      (![X24 : $i, X25 : $i]:
% 8.64/8.91         (~ (l1_pre_topc @ X24)
% 8.64/8.91          | ~ (v2_pre_topc @ X24)
% 8.64/8.91          | (v2_struct_0 @ X24)
% 8.64/8.91          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.64/8.91          | (l1_pre_topc @ (k6_tmap_1 @ X24 @ X25)))),
% 8.64/8.91      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 8.64/8.91  thf('51', plain,
% 8.64/8.91      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | (v2_struct_0 @ sk_A)
% 8.64/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91        | ~ (l1_pre_topc @ sk_A))),
% 8.64/8.91      inference('sup-', [status(thm)], ['49', '50'])).
% 8.64/8.91  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('54', plain,
% 8.64/8.91      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 8.64/8.91      inference('demod', [status(thm)], ['51', '52', '53'])).
% 8.64/8.91  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('56', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.64/8.91      inference('clc', [status(thm)], ['54', '55'])).
% 8.64/8.91  thf('57', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('58', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X1 @ 
% 8.64/8.91             (k1_zfmisc_1 @ 
% 8.64/8.91              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 8.64/8.91          | ~ (v1_funct_1 @ X1)
% 8.64/8.91          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 8.64/8.91          | (zip_tseitin_2 @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (l1_pre_topc @ X0))),
% 8.64/8.91      inference('demod', [status(thm)], ['48', '56', '57'])).
% 8.64/8.91  thf('59', plain,
% 8.64/8.91      (![X0 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X0 @ 
% 8.64/8.91             (k1_zfmisc_1 @ 
% 8.64/8.91              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.64/8.91          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91               (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91             (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 8.64/8.91               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91          | ~ (v1_funct_1 @ X0))),
% 8.64/8.91      inference('sup-', [status(thm)], ['45', '58'])).
% 8.64/8.91  thf('60', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.64/8.91      inference('clc', [status(thm)], ['54', '55'])).
% 8.64/8.91  thf('61', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('62', plain,
% 8.64/8.91      (![X0 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X0 @ 
% 8.64/8.91             (k1_zfmisc_1 @ 
% 8.64/8.91              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.64/8.91          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91               (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91             (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91          | ~ (v1_funct_1 @ X0))),
% 8.64/8.91      inference('demod', [status(thm)], ['59', '60', '61'])).
% 8.64/8.91  thf('63', plain,
% 8.64/8.91      (![X0 : $i]:
% 8.64/8.91         (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 8.64/8.91          | ~ (v1_funct_1 @ X0)
% 8.64/8.91          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91             (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (m1_subset_1 @ X0 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 8.64/8.91      inference('sup-', [status(thm)], ['44', '62'])).
% 8.64/8.91  thf('64', plain,
% 8.64/8.91      (![X2 : $i]:
% 8.64/8.91         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 8.64/8.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.64/8.91  thf('65', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('66', plain,
% 8.64/8.91      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 8.64/8.91        | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.64/8.91      inference('sup+', [status(thm)], ['64', '65'])).
% 8.64/8.91  thf('67', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.64/8.91      inference('clc', [status(thm)], ['54', '55'])).
% 8.64/8.91  thf('68', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 8.64/8.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.64/8.91  thf('69', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.64/8.91      inference('sup-', [status(thm)], ['67', '68'])).
% 8.64/8.91  thf('70', plain,
% 8.64/8.91      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('demod', [status(thm)], ['66', '69'])).
% 8.64/8.91  thf('71', plain,
% 8.64/8.91      (![X0 : $i]:
% 8.64/8.91         (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 8.64/8.91          | ~ (v1_funct_1 @ X0)
% 8.64/8.91          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91             (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (m1_subset_1 @ X0 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 8.64/8.91      inference('demod', [status(thm)], ['63', '70'])).
% 8.64/8.91  thf('72', plain,
% 8.64/8.91      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91         (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 8.64/8.91        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['43', '71'])).
% 8.64/8.91  thf('73', plain,
% 8.64/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('74', plain,
% 8.64/8.91      (![X26 : $i, X27 : $i]:
% 8.64/8.91         (~ (l1_pre_topc @ X26)
% 8.64/8.91          | ~ (v2_pre_topc @ X26)
% 8.64/8.91          | (v2_struct_0 @ X26)
% 8.64/8.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 8.64/8.91          | (v1_funct_2 @ (k7_tmap_1 @ X26 @ X27) @ (u1_struct_0 @ X26) @ 
% 8.64/8.91             (u1_struct_0 @ (k6_tmap_1 @ X26 @ X27))))),
% 8.64/8.91      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 8.64/8.91  thf('75', plain,
% 8.64/8.91      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 8.64/8.91         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91        | (v2_struct_0 @ sk_A)
% 8.64/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91        | ~ (l1_pre_topc @ sk_A))),
% 8.64/8.91      inference('sup-', [status(thm)], ['73', '74'])).
% 8.64/8.91  thf('76', plain,
% 8.64/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.64/8.91  thf('77', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('80', plain,
% 8.64/8.91      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91        | (v2_struct_0 @ sk_A))),
% 8.64/8.91      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 8.64/8.91  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('82', plain,
% 8.64/8.91      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['80', '81'])).
% 8.64/8.91  thf('83', plain,
% 8.64/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('84', plain,
% 8.64/8.91      (![X26 : $i, X27 : $i]:
% 8.64/8.91         (~ (l1_pre_topc @ X26)
% 8.64/8.91          | ~ (v2_pre_topc @ X26)
% 8.64/8.91          | (v2_struct_0 @ X26)
% 8.64/8.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 8.64/8.91          | (v1_funct_1 @ (k7_tmap_1 @ X26 @ X27)))),
% 8.64/8.91      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 8.64/8.91  thf('85', plain,
% 8.64/8.91      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | (v2_struct_0 @ sk_A)
% 8.64/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91        | ~ (l1_pre_topc @ sk_A))),
% 8.64/8.91      inference('sup-', [status(thm)], ['83', '84'])).
% 8.64/8.91  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('88', plain,
% 8.64/8.91      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 8.64/8.91      inference('demod', [status(thm)], ['85', '86', '87'])).
% 8.64/8.91  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('90', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 8.64/8.91      inference('clc', [status(thm)], ['88', '89'])).
% 8.64/8.91  thf('91', plain,
% 8.64/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.64/8.91  thf('92', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('demod', [status(thm)], ['90', '91'])).
% 8.64/8.91  thf('93', plain,
% 8.64/8.91      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91         (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 8.64/8.91      inference('demod', [status(thm)], ['72', '82', '92'])).
% 8.64/8.91  thf('94', plain,
% 8.64/8.91      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.64/8.91      inference('demod', [status(thm)], ['19', '20'])).
% 8.64/8.91  thf('95', plain,
% 8.64/8.91      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 8.64/8.91        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['93', '94'])).
% 8.64/8.91  thf('96', plain,
% 8.64/8.91      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.64/8.91        (k1_zfmisc_1 @ 
% 8.64/8.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 8.64/8.91      inference('clc', [status(thm)], ['41', '42'])).
% 8.64/8.91  thf('97', plain,
% 8.64/8.91      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('98', plain,
% 8.64/8.91      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.64/8.91      inference('split', [status(esa)], ['97'])).
% 8.64/8.91  thf('99', plain,
% 8.64/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf(t106_tmap_1, axiom,
% 8.64/8.91    (![A:$i]:
% 8.64/8.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.64/8.91       ( ![B:$i]:
% 8.64/8.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.64/8.91           ( ( v3_pre_topc @ B @ A ) <=>
% 8.64/8.91             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 8.64/8.91               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 8.64/8.91  thf('100', plain,
% 8.64/8.91      (![X36 : $i, X37 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 8.64/8.91          | ~ (v3_pre_topc @ X36 @ X37)
% 8.64/8.91          | ((g1_pre_topc @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37))
% 8.64/8.91              = (k6_tmap_1 @ X37 @ X36))
% 8.64/8.91          | ~ (l1_pre_topc @ X37)
% 8.64/8.91          | ~ (v2_pre_topc @ X37)
% 8.64/8.91          | (v2_struct_0 @ X37))),
% 8.64/8.91      inference('cnf', [status(esa)], [t106_tmap_1])).
% 8.64/8.91  thf('101', plain,
% 8.64/8.91      (((v2_struct_0 @ sk_A)
% 8.64/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91        | ~ (l1_pre_topc @ sk_A)
% 8.64/8.91        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 8.64/8.91            = (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 8.64/8.91      inference('sup-', [status(thm)], ['99', '100'])).
% 8.64/8.91  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('104', plain,
% 8.64/8.91      (((v2_struct_0 @ sk_A)
% 8.64/8.91        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 8.64/8.91            = (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 8.64/8.91      inference('demod', [status(thm)], ['101', '102', '103'])).
% 8.64/8.91  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('106', plain,
% 8.64/8.91      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 8.64/8.91        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 8.64/8.91            = (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.64/8.91      inference('clc', [status(thm)], ['104', '105'])).
% 8.64/8.91  thf('107', plain,
% 8.64/8.91      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 8.64/8.91          = (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['98', '106'])).
% 8.64/8.91  thf('108', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf(t62_pre_topc, axiom,
% 8.64/8.91    (![A:$i]:
% 8.64/8.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.64/8.91       ( ![B:$i]:
% 8.64/8.91         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 8.64/8.91           ( ![C:$i]:
% 8.64/8.91             ( ( ( v1_funct_1 @ C ) & 
% 8.64/8.91                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.64/8.91                 ( m1_subset_1 @
% 8.64/8.91                   C @ 
% 8.64/8.91                   ( k1_zfmisc_1 @
% 8.64/8.91                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.64/8.91               ( ![D:$i]:
% 8.64/8.91                 ( ( ( v1_funct_1 @ D ) & 
% 8.64/8.91                     ( v1_funct_2 @
% 8.64/8.91                       D @ 
% 8.64/8.91                       ( u1_struct_0 @
% 8.64/8.91                         ( g1_pre_topc @
% 8.64/8.91                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 8.64/8.91                       ( u1_struct_0 @ B ) ) & 
% 8.64/8.91                     ( m1_subset_1 @
% 8.64/8.91                       D @ 
% 8.64/8.91                       ( k1_zfmisc_1 @
% 8.64/8.91                         ( k2_zfmisc_1 @
% 8.64/8.91                           ( u1_struct_0 @
% 8.64/8.91                             ( g1_pre_topc @
% 8.64/8.91                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 8.64/8.91                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.64/8.91                   ( ( ( C ) = ( D ) ) =>
% 8.64/8.91                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 8.64/8.91                       ( v5_pre_topc @
% 8.64/8.91                         D @ 
% 8.64/8.91                         ( g1_pre_topc @
% 8.64/8.91                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 8.64/8.91                         B ) ) ) ) ) ) ) ) ) ))).
% 8.64/8.91  thf('109', plain,
% 8.64/8.91      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 8.64/8.91         (~ (v2_pre_topc @ X4)
% 8.64/8.91          | ~ (l1_pre_topc @ X4)
% 8.64/8.91          | ~ (v1_funct_1 @ X5)
% 8.64/8.91          | ~ (v1_funct_2 @ X5 @ 
% 8.64/8.91               (u1_struct_0 @ 
% 8.64/8.91                (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6))) @ 
% 8.64/8.91               (u1_struct_0 @ X4))
% 8.64/8.91          | ~ (m1_subset_1 @ X5 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ 
% 8.64/8.91                 (u1_struct_0 @ 
% 8.64/8.91                  (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6))) @ 
% 8.64/8.91                 (u1_struct_0 @ X4))))
% 8.64/8.91          | ~ (v5_pre_topc @ X5 @ 
% 8.64/8.91               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)) @ X4)
% 8.64/8.91          | (v5_pre_topc @ X7 @ X6 @ X4)
% 8.64/8.91          | ((X7) != (X5))
% 8.64/8.91          | ~ (m1_subset_1 @ X7 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 8.64/8.91          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 8.64/8.91          | ~ (v1_funct_1 @ X7)
% 8.64/8.91          | ~ (l1_pre_topc @ X6)
% 8.64/8.91          | ~ (v2_pre_topc @ X6))),
% 8.64/8.91      inference('cnf', [status(esa)], [t62_pre_topc])).
% 8.64/8.91  thf('110', plain,
% 8.64/8.91      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.64/8.91         (~ (v2_pre_topc @ X6)
% 8.64/8.91          | ~ (l1_pre_topc @ X6)
% 8.64/8.91          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 8.64/8.91          | ~ (m1_subset_1 @ X5 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 8.64/8.91          | (v5_pre_topc @ X5 @ X6 @ X4)
% 8.64/8.91          | ~ (v5_pre_topc @ X5 @ 
% 8.64/8.91               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)) @ X4)
% 8.64/8.91          | ~ (m1_subset_1 @ X5 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ 
% 8.64/8.91                 (u1_struct_0 @ 
% 8.64/8.91                  (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6))) @ 
% 8.64/8.91                 (u1_struct_0 @ X4))))
% 8.64/8.91          | ~ (v1_funct_2 @ X5 @ 
% 8.64/8.91               (u1_struct_0 @ 
% 8.64/8.91                (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6))) @ 
% 8.64/8.91               (u1_struct_0 @ X4))
% 8.64/8.91          | ~ (v1_funct_1 @ X5)
% 8.64/8.91          | ~ (l1_pre_topc @ X4)
% 8.64/8.91          | ~ (v2_pre_topc @ X4))),
% 8.64/8.91      inference('simplify', [status(thm)], ['109'])).
% 8.64/8.91  thf('111', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X1 @ 
% 8.64/8.91             (k1_zfmisc_1 @ 
% 8.64/8.91              (k2_zfmisc_1 @ 
% 8.64/8.91               (u1_struct_0 @ 
% 8.64/8.91                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 8.64/8.91               (u1_struct_0 @ sk_A))))
% 8.64/8.91          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (v1_funct_1 @ X1)
% 8.64/8.91          | ~ (v1_funct_2 @ X1 @ 
% 8.64/8.91               (u1_struct_0 @ 
% 8.64/8.91                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 8.64/8.91               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91          | ~ (v5_pre_topc @ X1 @ 
% 8.64/8.91               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 8.64/8.91               (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (m1_subset_1 @ X1 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 8.64/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 8.64/8.91          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ 
% 8.64/8.91               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91          | ~ (l1_pre_topc @ X0)
% 8.64/8.91          | ~ (v2_pre_topc @ X0))),
% 8.64/8.91      inference('sup-', [status(thm)], ['108', '110'])).
% 8.64/8.91  thf('112', plain,
% 8.64/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('113', plain,
% 8.64/8.91      (![X24 : $i, X25 : $i]:
% 8.64/8.91         (~ (l1_pre_topc @ X24)
% 8.64/8.91          | ~ (v2_pre_topc @ X24)
% 8.64/8.91          | (v2_struct_0 @ X24)
% 8.64/8.91          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.64/8.91          | (v2_pre_topc @ (k6_tmap_1 @ X24 @ X25)))),
% 8.64/8.91      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 8.64/8.91  thf('114', plain,
% 8.64/8.91      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | (v2_struct_0 @ sk_A)
% 8.64/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91        | ~ (l1_pre_topc @ sk_A))),
% 8.64/8.91      inference('sup-', [status(thm)], ['112', '113'])).
% 8.64/8.91  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('117', plain,
% 8.64/8.91      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 8.64/8.91      inference('demod', [status(thm)], ['114', '115', '116'])).
% 8.64/8.91  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('119', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.64/8.91      inference('clc', [status(thm)], ['117', '118'])).
% 8.64/8.91  thf('120', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.64/8.91      inference('clc', [status(thm)], ['54', '55'])).
% 8.64/8.91  thf('121', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('122', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('123', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('124', plain,
% 8.64/8.91      (![X0 : $i, X1 : $i]:
% 8.64/8.91         (~ (m1_subset_1 @ X1 @ 
% 8.64/8.91             (k1_zfmisc_1 @ 
% 8.64/8.91              (k2_zfmisc_1 @ 
% 8.64/8.91               (u1_struct_0 @ 
% 8.64/8.91                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 8.64/8.91               (u1_struct_0 @ sk_A))))
% 8.64/8.91          | ~ (v1_funct_1 @ X1)
% 8.64/8.91          | ~ (v1_funct_2 @ X1 @ 
% 8.64/8.91               (u1_struct_0 @ 
% 8.64/8.91                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 8.64/8.91               (u1_struct_0 @ sk_A))
% 8.64/8.91          | ~ (v5_pre_topc @ X1 @ 
% 8.64/8.91               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 8.64/8.91               (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91          | ~ (m1_subset_1 @ X1 @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 8.64/8.91          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 8.64/8.91          | ~ (l1_pre_topc @ X0)
% 8.64/8.91          | ~ (v2_pre_topc @ X0))),
% 8.64/8.91      inference('demod', [status(thm)],
% 8.64/8.91                ['111', '119', '120', '121', '122', '123'])).
% 8.64/8.91  thf('125', plain,
% 8.64/8.91      ((![X0 : $i]:
% 8.64/8.91          (~ (m1_subset_1 @ X0 @ 
% 8.64/8.91              (k1_zfmisc_1 @ 
% 8.64/8.91               (k2_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 8.64/8.91                (u1_struct_0 @ sk_A))))
% 8.64/8.91           | ~ (v2_pre_topc @ sk_A)
% 8.64/8.91           | ~ (l1_pre_topc @ sk_A)
% 8.64/8.91           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91           | ~ (m1_subset_1 @ X0 @ 
% 8.64/8.91                (k1_zfmisc_1 @ 
% 8.64/8.91                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.64/8.91           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91           | ~ (v5_pre_topc @ X0 @ 
% 8.64/8.91                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 8.64/8.91                (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91           | ~ (v1_funct_2 @ X0 @ 
% 8.64/8.91                (u1_struct_0 @ 
% 8.64/8.91                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 8.64/8.91                (u1_struct_0 @ sk_A))
% 8.64/8.91           | ~ (v1_funct_1 @ X0)))
% 8.64/8.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['107', '124'])).
% 8.64/8.91  thf('126', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('129', plain,
% 8.64/8.91      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 8.64/8.91          = (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['98', '106'])).
% 8.64/8.91  thf('130', plain,
% 8.64/8.91      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 8.64/8.91          = (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.64/8.91      inference('sup-', [status(thm)], ['98', '106'])).
% 8.64/8.91  thf('131', plain,
% 8.64/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.64/8.91  thf('132', plain,
% 8.64/8.91      ((![X0 : $i]:
% 8.64/8.91          (~ (m1_subset_1 @ X0 @ 
% 8.64/8.91              (k1_zfmisc_1 @ 
% 8.64/8.91               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.64/8.91           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91           | ~ (m1_subset_1 @ X0 @ 
% 8.64/8.91                (k1_zfmisc_1 @ 
% 8.64/8.91                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.64/8.91           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91           | ~ (v5_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91                (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91           | ~ (v1_funct_1 @ X0)))
% 8.64/8.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.64/8.91      inference('demod', [status(thm)],
% 8.64/8.91                ['125', '126', '127', '128', '129', '130', '131'])).
% 8.64/8.91  thf('133', plain,
% 8.64/8.91      ((![X0 : $i]:
% 8.64/8.91          (~ (v1_funct_1 @ X0)
% 8.64/8.91           | ~ (v5_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91                (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.64/8.91           | ~ (m1_subset_1 @ X0 @ 
% 8.64/8.91                (k1_zfmisc_1 @ 
% 8.64/8.91                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))))
% 8.64/8.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 8.64/8.91      inference('simplify', [status(thm)], ['132'])).
% 8.64/8.91  thf('134', plain,
% 8.64/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.64/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.64/8.91  thf('135', plain,
% 8.64/8.91      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.64/8.91         (k6_tmap_1 @ sk_A @ sk_B))
% 8.64/8.91        | (v3_pre_topc @ sk_B @ sk_A))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('136', plain,
% 8.64/8.91      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.64/8.91         (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.64/8.91               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.64/8.91      inference('split', [status(esa)], ['135'])).
% 8.64/8.91  thf('137', plain,
% 8.64/8.91      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 8.64/8.91         (k6_tmap_1 @ sk_A @ sk_B)))
% 8.64/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.64/8.91               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.64/8.91      inference('sup+', [status(thm)], ['134', '136'])).
% 8.64/8.91  thf('138', plain,
% 8.64/8.91      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.64/8.91      inference('demod', [status(thm)], ['66', '69'])).
% 8.64/8.91  thf('139', plain,
% 8.64/8.91      (![X2 : $i]:
% 8.64/8.91         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 8.64/8.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.64/8.91  thf('140', plain,
% 8.64/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91         (k1_zfmisc_1 @ 
% 8.64/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.64/8.91           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 8.64/8.91        | (v3_pre_topc @ sk_B @ sk_A))),
% 8.64/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.64/8.91  thf('141', plain,
% 8.64/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91         (k1_zfmisc_1 @ 
% 8.64/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.64/8.91           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 8.64/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.64/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.64/8.91      inference('split', [status(esa)], ['140'])).
% 8.64/8.91  thf('142', plain,
% 8.64/8.91      ((((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91          (k1_zfmisc_1 @ 
% 8.64/8.91           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.64/8.91            (k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 8.64/8.91         | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 8.64/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.64/8.91               (k1_zfmisc_1 @ 
% 8.64/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('sup+', [status(thm)], ['139', '141'])).
% 8.75/8.91  thf('143', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.91      inference('sup-', [status(thm)], ['67', '68'])).
% 8.75/8.91  thf('144', plain,
% 8.75/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91         (k1_zfmisc_1 @ 
% 8.75/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91           (k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 8.75/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('demod', [status(thm)], ['142', '143'])).
% 8.75/8.91  thf('145', plain,
% 8.75/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91         (k1_zfmisc_1 @ 
% 8.75/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 8.75/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('sup+', [status(thm)], ['138', '144'])).
% 8.75/8.91  thf('146', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('147', plain,
% 8.75/8.91      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91         (k1_zfmisc_1 @ 
% 8.75/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 8.75/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('demod', [status(thm)], ['145', '146'])).
% 8.75/8.91  thf('148', plain,
% 8.75/8.91      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91           (k1_zfmisc_1 @ 
% 8.75/8.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 8.75/8.91        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91             (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 8.75/8.91        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('149', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('150', plain,
% 8.75/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.91  thf('151', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('152', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('153', plain,
% 8.75/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.91  thf('154', plain,
% 8.75/8.91      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['80', '81'])).
% 8.75/8.91  thf('155', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('156', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('demod', [status(thm)], ['90', '91'])).
% 8.75/8.91  thf('157', plain,
% 8.75/8.91      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91           (k1_zfmisc_1 @ 
% 8.75/8.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.75/8.91        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 8.75/8.91             (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 8.75/8.91      inference('demod', [status(thm)],
% 8.75/8.91                ['148', '149', '150', '151', '152', '153', '154', '155', '156'])).
% 8.75/8.91  thf('158', plain,
% 8.75/8.91      (((~ (v3_pre_topc @ sk_B @ sk_A)
% 8.75/8.91         | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 8.75/8.91              (k6_tmap_1 @ sk_A @ sk_B))))
% 8.75/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('sup-', [status(thm)], ['147', '157'])).
% 8.75/8.91  thf('159', plain,
% 8.75/8.91      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 8.75/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91               (k6_tmap_1 @ sk_A @ sk_B))) & 
% 8.75/8.91             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('sup-', [status(thm)], ['137', '158'])).
% 8.75/8.91  thf('160', plain,
% 8.75/8.91      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91        (k1_zfmisc_1 @ 
% 8.75/8.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 8.75/8.91      inference('clc', [status(thm)], ['41', '42'])).
% 8.75/8.91  thf('161', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('162', plain,
% 8.75/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.91  thf('163', plain,
% 8.75/8.91      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91           (k1_zfmisc_1 @ 
% 8.75/8.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 8.75/8.91        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91             (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 8.75/8.91        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('164', plain,
% 8.75/8.91      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91           (k1_zfmisc_1 @ 
% 8.75/8.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 8.75/8.91         <= (~
% 8.75/8.91             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('split', [status(esa)], ['163'])).
% 8.75/8.91  thf('165', plain,
% 8.75/8.91      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91           (k1_zfmisc_1 @ 
% 8.75/8.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 8.75/8.91         <= (~
% 8.75/8.91             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('sup-', [status(thm)], ['162', '164'])).
% 8.75/8.91  thf('166', plain,
% 8.75/8.91      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91           (k1_zfmisc_1 @ 
% 8.75/8.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 8.75/8.91         <= (~
% 8.75/8.91             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('sup-', [status(thm)], ['161', '165'])).
% 8.75/8.91  thf('167', plain,
% 8.75/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91         (k1_zfmisc_1 @ 
% 8.75/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 8.75/8.91      inference('sup-', [status(thm)], ['160', '166'])).
% 8.75/8.91  thf('168', plain,
% 8.75/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91         (k1_zfmisc_1 @ 
% 8.75/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 8.75/8.91      inference('sat_resolution*', [status(thm)], ['167'])).
% 8.75/8.91  thf('169', plain,
% 8.75/8.91      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 8.75/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.91      inference('simpl_trail', [status(thm)], ['159', '168'])).
% 8.75/8.91  thf('170', plain,
% 8.75/8.91      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91         (k6_tmap_1 @ sk_A @ sk_B)))
% 8.75/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.91      inference('split', [status(esa)], ['135'])).
% 8.75/8.91  thf('171', plain,
% 8.75/8.91      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 8.75/8.91         (~ (v5_pre_topc @ X17 @ X15 @ X16)
% 8.75/8.91          | (zip_tseitin_1 @ X18 @ X17 @ X16 @ X15)
% 8.75/8.91          | ~ (zip_tseitin_2 @ X17 @ X16 @ X15))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 8.75/8.91  thf('172', plain,
% 8.75/8.91      ((![X0 : $i]:
% 8.75/8.91          (~ (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.91           | (zip_tseitin_1 @ X0 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 8.75/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.91      inference('sup-', [status(thm)], ['170', '171'])).
% 8.75/8.91  thf('173', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('174', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('175', plain,
% 8.75/8.91      ((![X0 : $i]:
% 8.75/8.91          (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.91           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 8.75/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.91      inference('demod', [status(thm)], ['172', '173', '174'])).
% 8.75/8.91  thf('176', plain,
% 8.75/8.91      (![X8 : $i, X9 : $i]:
% 8.75/8.91         ((zip_tseitin_0 @ X8 @ X9) | ((k2_struct_0 @ X8) = (k1_xboole_0)))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.75/8.91  thf('177', plain,
% 8.75/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91         (k1_zfmisc_1 @ 
% 8.75/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 8.75/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('split', [status(esa)], ['140'])).
% 8.75/8.91  thf('178', plain,
% 8.75/8.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.75/8.91         (~ (l1_pre_topc @ X19)
% 8.75/8.91          | ~ (zip_tseitin_0 @ X19 @ X20)
% 8.75/8.91          | (zip_tseitin_2 @ X21 @ X19 @ X20)
% 8.75/8.91          | ~ (m1_subset_1 @ X21 @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 8.75/8.91          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 8.75/8.91          | ~ (v1_funct_1 @ X21)
% 8.75/8.91          | ~ (l1_pre_topc @ X20))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 8.75/8.91  thf('179', plain,
% 8.75/8.91      (((~ (l1_pre_topc @ sk_A)
% 8.75/8.91         | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91         | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91              (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 8.75/8.91         | (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91            (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.91         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.91         | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 8.75/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('sup-', [status(thm)], ['177', '178'])).
% 8.75/8.91  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('181', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.91      inference('clc', [status(thm)], ['88', '89'])).
% 8.75/8.91  thf('182', plain,
% 8.75/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.91  thf('183', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.91      inference('clc', [status(thm)], ['54', '55'])).
% 8.75/8.91  thf('184', plain,
% 8.75/8.91      (((~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91            (u1_struct_0 @ sk_A))
% 8.75/8.91         | (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91            (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.91         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 8.75/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('demod', [status(thm)], ['179', '180', '181', '182', '183'])).
% 8.75/8.91  thf('185', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('186', plain,
% 8.75/8.91      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['80', '81'])).
% 8.75/8.91  thf('187', plain,
% 8.75/8.91      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.91  thf('188', plain,
% 8.75/8.91      ((((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91          (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.91         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 8.75/8.91         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91               (k1_zfmisc_1 @ 
% 8.75/8.91                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 8.75/8.91      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 8.75/8.91  thf('189', plain,
% 8.75/8.91      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.91         (k1_zfmisc_1 @ 
% 8.75/8.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.91           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 8.75/8.91      inference('sat_resolution*', [status(thm)], ['167'])).
% 8.75/8.91  thf('190', plain,
% 8.75/8.91      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.91        | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 8.75/8.91      inference('simpl_trail', [status(thm)], ['188', '189'])).
% 8.75/8.91  thf('191', plain,
% 8.75/8.91      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 8.75/8.91        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 8.75/8.91      inference('sup-', [status(thm)], ['176', '190'])).
% 8.75/8.91  thf('192', plain,
% 8.75/8.91      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('demod', [status(thm)], ['66', '69'])).
% 8.75/8.91  thf('193', plain,
% 8.75/8.91      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 8.75/8.91        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 8.75/8.91      inference('demod', [status(thm)], ['191', '192'])).
% 8.75/8.91  thf('194', plain,
% 8.75/8.91      ((![X0 : $i]:
% 8.75/8.91          (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.91           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 8.75/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.91      inference('demod', [status(thm)], ['172', '173', '174'])).
% 8.75/8.91  thf('195', plain,
% 8.75/8.91      ((![X0 : $i]:
% 8.75/8.91          (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 8.75/8.91           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.91              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 8.75/8.91         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.91               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.91      inference('sup-', [status(thm)], ['193', '194'])).
% 8.75/8.91  thf('196', plain,
% 8.75/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('197', plain,
% 8.75/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.91  thf('198', plain,
% 8.75/8.91      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 8.75/8.91         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 8.75/8.91          | (v3_pre_topc @ 
% 8.75/8.91             (k8_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13 @ 
% 8.75/8.91              X10) @ 
% 8.75/8.91             X12)
% 8.75/8.91          | ~ (v3_pre_topc @ X10 @ X11)
% 8.75/8.91          | ~ (zip_tseitin_1 @ X10 @ X13 @ X11 @ X12))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.75/8.91  thf('199', plain,
% 8.75/8.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.75/8.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.75/8.91          | ~ (zip_tseitin_1 @ X0 @ X2 @ (k6_tmap_1 @ sk_A @ sk_B) @ X1)
% 8.75/8.91          | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91          | (v3_pre_topc @ 
% 8.75/8.91             (k8_relset_1 @ (u1_struct_0 @ X1) @ 
% 8.75/8.91              (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ X2 @ X0) @ 
% 8.75/8.91             X1))),
% 8.75/8.91      inference('sup-', [status(thm)], ['197', '198'])).
% 8.75/8.91  thf('200', plain,
% 8.75/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.91  thf('201', plain,
% 8.75/8.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.75/8.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.75/8.91          | ~ (zip_tseitin_1 @ X0 @ X2 @ (k6_tmap_1 @ sk_A @ sk_B) @ X1)
% 8.75/8.91          | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91          | (v3_pre_topc @ 
% 8.75/8.91             (k8_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_A) @ X2 @ X0) @ 
% 8.75/8.91             X1))),
% 8.75/8.91      inference('demod', [status(thm)], ['199', '200'])).
% 8.75/8.91  thf('202', plain,
% 8.75/8.91      (![X0 : $i, X1 : $i]:
% 8.75/8.91         ((v3_pre_topc @ 
% 8.75/8.91           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 8.75/8.91           X0)
% 8.75/8.91          | ~ (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 8.75/8.91      inference('sup-', [status(thm)], ['196', '201'])).
% 8.75/8.91  thf('203', plain,
% 8.75/8.91      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.91      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.91  thf(t105_tmap_1, axiom,
% 8.75/8.91    (![A:$i]:
% 8.75/8.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.75/8.91       ( ![B:$i]:
% 8.75/8.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.75/8.91           ( ![C:$i]:
% 8.75/8.91             ( ( m1_subset_1 @
% 8.75/8.91                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 8.75/8.91               ( ( ( C ) = ( B ) ) =>
% 8.75/8.91                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 8.75/8.91  thf('204', plain,
% 8.75/8.91      (![X33 : $i, X34 : $i, X35 : $i]:
% 8.75/8.91         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 8.75/8.91          | ((X35) != (X33))
% 8.75/8.91          | (v3_pre_topc @ X35 @ (k6_tmap_1 @ X34 @ X33))
% 8.75/8.91          | ~ (m1_subset_1 @ X35 @ 
% 8.75/8.91               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X34 @ X33))))
% 8.75/8.91          | ~ (l1_pre_topc @ X34)
% 8.75/8.91          | ~ (v2_pre_topc @ X34)
% 8.75/8.91          | (v2_struct_0 @ X34))),
% 8.75/8.91      inference('cnf', [status(esa)], [t105_tmap_1])).
% 8.75/8.91  thf('205', plain,
% 8.75/8.91      (![X33 : $i, X34 : $i]:
% 8.75/8.91         ((v2_struct_0 @ X34)
% 8.75/8.91          | ~ (v2_pre_topc @ X34)
% 8.75/8.91          | ~ (l1_pre_topc @ X34)
% 8.75/8.91          | ~ (m1_subset_1 @ X33 @ 
% 8.75/8.91               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X34 @ X33))))
% 8.75/8.91          | (v3_pre_topc @ X33 @ (k6_tmap_1 @ X34 @ X33))
% 8.75/8.91          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 8.75/8.91      inference('simplify', [status(thm)], ['204'])).
% 8.75/8.91  thf('206', plain,
% 8.75/8.91      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.75/8.91        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.75/8.91        | (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.91        | ~ (l1_pre_topc @ sk_A)
% 8.75/8.91        | ~ (v2_pre_topc @ sk_A)
% 8.75/8.91        | (v2_struct_0 @ sk_A))),
% 8.75/8.91      inference('sup-', [status(thm)], ['203', '205'])).
% 8.75/8.91  thf('207', plain,
% 8.75/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('208', plain,
% 8.75/8.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('210', plain, ((v2_pre_topc @ sk_A)),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('211', plain,
% 8.75/8.91      (((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 8.75/8.91      inference('demod', [status(thm)], ['206', '207', '208', '209', '210'])).
% 8.75/8.91  thf('212', plain, (~ (v2_struct_0 @ sk_A)),
% 8.75/8.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.91  thf('213', plain, ((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.91      inference('clc', [status(thm)], ['211', '212'])).
% 8.75/8.91  thf('214', plain,
% 8.75/8.91      (![X0 : $i, X1 : $i]:
% 8.75/8.91         ((v3_pre_topc @ 
% 8.75/8.91           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 8.75/8.91           X0)
% 8.75/8.91          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 8.75/8.91      inference('demod', [status(thm)], ['202', '213'])).
% 8.75/8.91  thf('215', plain,
% 8.75/8.91      (((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 8.75/8.91         | (v3_pre_topc @ 
% 8.75/8.91            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.92             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 8.75/8.92            sk_A)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('sup-', [status(thm)], ['195', '214'])).
% 8.75/8.92  thf('216', plain,
% 8.75/8.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.75/8.92  thf('217', plain,
% 8.75/8.92      (![X0 : $i, X1 : $i]:
% 8.75/8.92         (((k8_relset_1 @ X1 @ X1 @ (k6_partfun1 @ X1) @ X0) = (X0))
% 8.75/8.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 8.75/8.92      inference('cnf', [status(esa)], [t171_funct_2])).
% 8.75/8.92  thf('218', plain,
% 8.75/8.92      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.92         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 8.75/8.92      inference('sup-', [status(thm)], ['216', '217'])).
% 8.75/8.92  thf('219', plain,
% 8.75/8.92      (((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v3_pre_topc @ sk_B @ sk_A)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('demod', [status(thm)], ['215', '218'])).
% 8.75/8.92  thf('220', plain,
% 8.75/8.92      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('simpl_trail', [status(thm)], ['159', '168'])).
% 8.75/8.92  thf('221', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('222', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('223', plain,
% 8.75/8.92      ((![X0 : $i]:
% 8.75/8.92          (~ (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.92           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('demod', [status(thm)], ['175', '221', '222'])).
% 8.75/8.92  thf('224', plain,
% 8.75/8.92      (![X2 : $i]:
% 8.75/8.92         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 8.75/8.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.75/8.92  thf('225', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('226', plain,
% 8.75/8.92      (((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('sup+', [status(thm)], ['224', '225'])).
% 8.75/8.92  thf('227', plain, ((l1_struct_0 @ sk_A)),
% 8.75/8.92      inference('sup-', [status(thm)], ['23', '24'])).
% 8.75/8.92  thf('228', plain,
% 8.75/8.92      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('demod', [status(thm)], ['226', '227'])).
% 8.75/8.92  thf('229', plain,
% 8.75/8.92      (![X8 : $i, X9 : $i]:
% 8.75/8.92         ((zip_tseitin_0 @ X8 @ X9) | ((k2_struct_0 @ X9) != (k1_xboole_0)))),
% 8.75/8.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.75/8.92  thf('230', plain,
% 8.75/8.92      ((![X0 : $i]:
% 8.75/8.92          (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ sk_A)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('sup-', [status(thm)], ['228', '229'])).
% 8.75/8.92  thf('231', plain,
% 8.75/8.92      ((![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_A))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('simplify', [status(thm)], ['230'])).
% 8.75/8.92  thf('232', plain,
% 8.75/8.92      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 8.75/8.92        | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 8.75/8.92      inference('simpl_trail', [status(thm)], ['188', '189'])).
% 8.75/8.92  thf('233', plain,
% 8.75/8.92      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('sup-', [status(thm)], ['231', '232'])).
% 8.75/8.92  thf('234', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('235', plain,
% 8.75/8.92      (((zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('demod', [status(thm)], ['233', '234'])).
% 8.75/8.92  thf('236', plain,
% 8.75/8.92      ((![X0 : $i]:
% 8.75/8.92          (zip_tseitin_1 @ X0 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('demod', [status(thm)], ['223', '235'])).
% 8.75/8.92  thf('237', plain,
% 8.75/8.92      (![X0 : $i, X1 : $i]:
% 8.75/8.92         ((v3_pre_topc @ 
% 8.75/8.92           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 8.75/8.92           X0)
% 8.75/8.92          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 8.75/8.92      inference('demod', [status(thm)], ['202', '213'])).
% 8.75/8.92  thf('238', plain,
% 8.75/8.92      (((v3_pre_topc @ 
% 8.75/8.92         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.92          (k6_partfun1 @ k1_xboole_0) @ sk_B) @ 
% 8.75/8.92         sk_A))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('sup-', [status(thm)], ['236', '237'])).
% 8.75/8.92  thf('239', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('240', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('241', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('242', plain,
% 8.75/8.92      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.92         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 8.75/8.92      inference('sup-', [status(thm)], ['216', '217'])).
% 8.75/8.92  thf('243', plain,
% 8.75/8.92      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 8.75/8.92          (k6_partfun1 @ k1_xboole_0) @ sk_B) = (sk_B)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('sup+', [status(thm)], ['241', '242'])).
% 8.75/8.92  thf('244', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('245', plain,
% 8.75/8.92      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('clc', [status(thm)], ['219', '220'])).
% 8.75/8.92  thf('246', plain,
% 8.75/8.92      ((((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 8.75/8.92          (k6_partfun1 @ k1_xboole_0) @ sk_B) = (sk_B)))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('demod', [status(thm)], ['243', '244', '245'])).
% 8.75/8.92  thf('247', plain,
% 8.75/8.92      (((v3_pre_topc @ sk_B @ sk_A))
% 8.75/8.92         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('demod', [status(thm)], ['238', '239', '240', '246'])).
% 8.75/8.92  thf('248', plain,
% 8.75/8.92      (~
% 8.75/8.92       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92         (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('demod', [status(thm)], ['169', '247'])).
% 8.75/8.92  thf('249', plain,
% 8.75/8.92      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 8.75/8.92       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92         (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('split', [status(esa)], ['135'])).
% 8.75/8.92  thf('250', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 8.75/8.92      inference('sat_resolution*', [status(thm)], ['248', '249'])).
% 8.75/8.92  thf('251', plain,
% 8.75/8.92      (![X0 : $i]:
% 8.75/8.92         (~ (v1_funct_1 @ X0)
% 8.75/8.92          | ~ (v5_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92          | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.75/8.92          | ~ (m1_subset_1 @ X0 @ 
% 8.75/8.92               (k1_zfmisc_1 @ 
% 8.75/8.92                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 8.75/8.92      inference('simpl_trail', [status(thm)], ['133', '250'])).
% 8.75/8.92  thf('252', plain,
% 8.75/8.92      ((~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.75/8.92        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92             (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 8.75/8.92      inference('sup-', [status(thm)], ['96', '251'])).
% 8.75/8.92  thf('253', plain,
% 8.75/8.92      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 8.75/8.92      inference('clc', [status(thm)], ['80', '81'])).
% 8.75/8.92  thf('254', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.92      inference('demod', [status(thm)], ['90', '91'])).
% 8.75/8.92  thf('255', plain,
% 8.75/8.92      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 8.75/8.92         (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92             (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('demod', [status(thm)], ['252', '253', '254'])).
% 8.75/8.92  thf('256', plain,
% 8.75/8.92      ((~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B)))
% 8.75/8.92         <= (~
% 8.75/8.92             ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('split', [status(esa)], ['163'])).
% 8.75/8.92  thf('257', plain,
% 8.75/8.92      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.92      inference('clc', [status(thm)], ['35', '36'])).
% 8.75/8.92  thf('258', plain,
% 8.75/8.92      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B)))
% 8.75/8.92         <= (~
% 8.75/8.92             ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))))),
% 8.75/8.92      inference('demod', [status(thm)], ['256', '257'])).
% 8.75/8.92  thf('259', plain,
% 8.75/8.92      (~
% 8.75/8.92       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 8.75/8.92         (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('sat_resolution*', [status(thm)], ['248'])).
% 8.75/8.92  thf('260', plain,
% 8.75/8.92      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 8.75/8.92          (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('simpl_trail', [status(thm)], ['258', '259'])).
% 8.75/8.92  thf('261', plain,
% 8.75/8.92      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('clc', [status(thm)], ['255', '260'])).
% 8.75/8.92  thf('262', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('263', plain,
% 8.75/8.92      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92        | (v5_pre_topc @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('demod', [status(thm)], ['26', '262'])).
% 8.75/8.92  thf('264', plain,
% 8.75/8.92      (![X2 : $i]:
% 8.75/8.92         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 8.75/8.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.75/8.92  thf('265', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('266', plain,
% 8.75/8.92      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 8.75/8.92      inference('sup+', [status(thm)], ['264', '265'])).
% 8.75/8.92  thf('267', plain, ((l1_struct_0 @ sk_A)),
% 8.75/8.92      inference('sup-', [status(thm)], ['23', '24'])).
% 8.75/8.92  thf('268', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('demod', [status(thm)], ['266', '267'])).
% 8.75/8.92  thf('269', plain,
% 8.75/8.92      ((~ (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92        | (v5_pre_topc @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('demod', [status(thm)], ['263', '268'])).
% 8.75/8.92  thf('270', plain,
% 8.75/8.92      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('clc', [status(thm)], ['255', '260'])).
% 8.75/8.92  thf('271', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('272', plain,
% 8.75/8.92      (~ (v5_pre_topc @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('demod', [status(thm)], ['270', '271'])).
% 8.75/8.92  thf('273', plain,
% 8.75/8.92      (~ (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('clc', [status(thm)], ['269', '272'])).
% 8.75/8.92  thf('274', plain,
% 8.75/8.92      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92        (k1_zfmisc_1 @ 
% 8.75/8.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 8.75/8.92      inference('clc', [status(thm)], ['41', '42'])).
% 8.75/8.92  thf('275', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('276', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('277', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('278', plain,
% 8.75/8.92      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 8.75/8.92      inference('demod', [status(thm)], ['274', '275', '276', '277'])).
% 8.75/8.92  thf('279', plain,
% 8.75/8.92      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.92      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.92  thf('280', plain,
% 8.75/8.92      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.92      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.92  thf('281', plain,
% 8.75/8.92      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.75/8.92         (~ (l1_pre_topc @ X19)
% 8.75/8.92          | ~ (zip_tseitin_0 @ X19 @ X20)
% 8.75/8.92          | (zip_tseitin_2 @ X21 @ X19 @ X20)
% 8.75/8.92          | ~ (m1_subset_1 @ X21 @ 
% 8.75/8.92               (k1_zfmisc_1 @ 
% 8.75/8.92                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 8.75/8.92          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 8.75/8.92          | ~ (v1_funct_1 @ X21)
% 8.75/8.92          | ~ (l1_pre_topc @ X20))),
% 8.75/8.92      inference('cnf', [status(esa)], [zf_stmt_7])).
% 8.75/8.92  thf('282', plain,
% 8.75/8.92      (![X0 : $i, X1 : $i]:
% 8.75/8.92         (~ (m1_subset_1 @ X1 @ 
% 8.75/8.92             (k1_zfmisc_1 @ 
% 8.75/8.92              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 8.75/8.92          | ~ (l1_pre_topc @ X0)
% 8.75/8.92          | ~ (v1_funct_1 @ X1)
% 8.75/8.92          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ 
% 8.75/8.92               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 8.75/8.92          | (zip_tseitin_2 @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0)
% 8.75/8.92          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0)
% 8.75/8.92          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('sup-', [status(thm)], ['280', '281'])).
% 8.75/8.92  thf('283', plain,
% 8.75/8.92      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.92      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.92  thf('284', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('clc', [status(thm)], ['54', '55'])).
% 8.75/8.92  thf('285', plain,
% 8.75/8.92      (![X0 : $i, X1 : $i]:
% 8.75/8.92         (~ (m1_subset_1 @ X1 @ 
% 8.75/8.92             (k1_zfmisc_1 @ 
% 8.75/8.92              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 8.75/8.92          | ~ (l1_pre_topc @ X0)
% 8.75/8.92          | ~ (v1_funct_1 @ X1)
% 8.75/8.92          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 8.75/8.92          | (zip_tseitin_2 @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0)
% 8.75/8.92          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 8.75/8.92      inference('demod', [status(thm)], ['282', '283', '284'])).
% 8.75/8.92  thf('286', plain,
% 8.75/8.92      (![X0 : $i]:
% 8.75/8.92         (~ (m1_subset_1 @ X0 @ 
% 8.75/8.92             (k1_zfmisc_1 @ 
% 8.75/8.92              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.75/8.92          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.92             (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 8.75/8.92               (u1_struct_0 @ sk_A))
% 8.75/8.92          | ~ (v1_funct_1 @ X0)
% 8.75/8.92          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('sup-', [status(thm)], ['279', '285'])).
% 8.75/8.92  thf('287', plain,
% 8.75/8.92      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.92      inference('clc', [status(thm)], ['6', '7'])).
% 8.75/8.92  thf('288', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('clc', [status(thm)], ['54', '55'])).
% 8.75/8.92  thf('289', plain,
% 8.75/8.92      (![X0 : $i]:
% 8.75/8.92         (~ (m1_subset_1 @ X0 @ 
% 8.75/8.92             (k1_zfmisc_1 @ 
% 8.75/8.92              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 8.75/8.92          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.92               (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.92             (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 8.75/8.92          | ~ (v1_funct_1 @ X0))),
% 8.75/8.92      inference('demod', [status(thm)], ['286', '287', '288'])).
% 8.75/8.92  thf('290', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('291', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('292', plain,
% 8.75/8.92      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 8.75/8.92      inference('demod', [status(thm)], ['66', '69'])).
% 8.75/8.92  thf('293', plain,
% 8.75/8.92      (![X8 : $i, X9 : $i]:
% 8.75/8.92         ((zip_tseitin_0 @ X8 @ X9) | ((k2_struct_0 @ X9) != (k1_xboole_0)))),
% 8.75/8.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.75/8.92  thf('294', plain,
% 8.75/8.92      (![X0 : $i]:
% 8.75/8.92         (((u1_struct_0 @ sk_A) != (k1_xboole_0))
% 8.75/8.92          | (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('sup-', [status(thm)], ['292', '293'])).
% 8.75/8.92  thf('295', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('296', plain,
% 8.75/8.92      (![X0 : $i]:
% 8.75/8.92         (((k1_xboole_0) != (k1_xboole_0))
% 8.75/8.92          | (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('demod', [status(thm)], ['294', '295'])).
% 8.75/8.92  thf('297', plain,
% 8.75/8.92      (![X0 : $i]: (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('simplify', [status(thm)], ['296'])).
% 8.75/8.92  thf('298', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('299', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('300', plain,
% 8.75/8.92      (![X0 : $i]:
% 8.75/8.92         (~ (m1_subset_1 @ X0 @ 
% 8.75/8.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 8.75/8.92          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 8.75/8.92             (k6_tmap_1 @ sk_A @ sk_B))
% 8.75/8.92          | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 8.75/8.92          | ~ (v1_funct_1 @ X0))),
% 8.75/8.92      inference('demod', [status(thm)],
% 8.75/8.92                ['289', '290', '291', '297', '298', '299'])).
% 8.75/8.92  thf('301', plain,
% 8.75/8.92      ((~ (v1_funct_1 @ (k6_partfun1 @ k1_xboole_0))
% 8.75/8.92        | ~ (v1_funct_2 @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0 @ 
% 8.75/8.92             k1_xboole_0)
% 8.75/8.92        | (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 8.75/8.92      inference('sup-', [status(thm)], ['278', '300'])).
% 8.75/8.92  thf('302', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 8.75/8.92      inference('demod', [status(thm)], ['90', '91'])).
% 8.75/8.92  thf('303', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('304', plain, ((v1_funct_1 @ (k6_partfun1 @ k1_xboole_0))),
% 8.75/8.92      inference('demod', [status(thm)], ['302', '303'])).
% 8.75/8.92  thf('305', plain,
% 8.75/8.92      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 8.75/8.92        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 8.75/8.92      inference('clc', [status(thm)], ['80', '81'])).
% 8.75/8.92  thf('306', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('307', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('308', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.75/8.92      inference('clc', [status(thm)], ['95', '261'])).
% 8.75/8.92  thf('309', plain,
% 8.75/8.92      ((v1_funct_2 @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0 @ k1_xboole_0)),
% 8.75/8.92      inference('demod', [status(thm)], ['305', '306', '307', '308'])).
% 8.75/8.92  thf('310', plain,
% 8.75/8.92      ((zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 8.75/8.92        (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 8.75/8.92      inference('demod', [status(thm)], ['301', '304', '309'])).
% 8.75/8.92  thf('311', plain, ($false), inference('demod', [status(thm)], ['273', '310'])).
% 8.75/8.92  
% 8.75/8.92  % SZS output end Refutation
% 8.75/8.92  
% 8.75/8.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
