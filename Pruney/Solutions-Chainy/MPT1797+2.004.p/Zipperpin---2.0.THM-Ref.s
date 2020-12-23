%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qj21EfbVC5

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:53 EST 2020

% Result     : Theorem 6.94s
% Output     : Refutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :  423 (601069 expanded)
%              Number of leaves         :   49 (169911 expanded)
%              Depth                    :   38
%              Number of atoms          : 5139 (15846752 expanded)
%              Number of equality atoms :  175 (154484 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X36 @ X35 ) )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
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
    ! [X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_1 @ X16 @ X19 @ X17 @ X20 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relset_1 @ X5 @ X5 @ ( k6_partfun1 @ X5 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X0 @ X2 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_1 @ X16 @ X19 @ X17 @ X20 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X17 ) @ X19 @ X16 ) @ X20 ) ) ),
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
    ! [X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_1 @ X16 @ X19 @ X17 @ X20 )
      | ( v3_pre_topc @ X16 @ X17 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X21 @ X22 @ X23 ) @ X23 @ X22 @ X21 )
      | ( v5_pre_topc @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_2 @ X23 @ X22 @ X21 ) ) ),
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
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X32 @ X33 ) ) ) ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k7_tmap_1 @ X29 @ X28 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( ( k2_struct_0 @ X14 )
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X30 @ X31 ) ) ) ),
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
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
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
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X32 @ X33 ) @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X32 @ X33 ) ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v3_pre_topc @ X40 @ X41 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) )
        = ( k6_tmap_1 @ X41 @ X40 ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v5_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) @ X10 )
      | ( v5_pre_topc @ X13 @ X12 @ X10 )
      | ( X13 != X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( v5_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X30 @ X31 ) ) ) ),
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
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('139',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('140',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['140'])).

thf('142',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['139','141'])).

thf('143',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['138','142'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('146',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('147',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('148',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('149',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('150',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('151',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('152',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('153',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['144','145','146','147','148','149','150','151','152'])).

thf('154',plain,
    ( ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['143','153'])).

thf('155',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','154'])).

thf('156',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('157',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('158',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('159',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['159'])).

thf('161',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['158','160'])).

thf('162',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['157','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['163'])).

thf('165',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['155','164'])).

thf('166',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['135'])).

thf('167',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v5_pre_topc @ X23 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X24 @ X23 @ X22 @ X21 )
      | ~ ( zip_tseitin_2 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('168',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('170',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('171',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( ( k2_struct_0 @ X14 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('173',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['140'])).

thf('174',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('175',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('178',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('179',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('180',plain,
    ( ( ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['175','176','177','178','179'])).

thf('181',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('182',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('183',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('184',plain,
    ( ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['163'])).

thf('186',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['172','186'])).

thf('188',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('189',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('191',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ sk_A )
          = k1_xboole_0 )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('194',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 @ X16 ) @ X18 )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X16 @ X19 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['192','197'])).

thf('199',plain,
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

thf('200',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( X39 != X37 )
      | ( v3_pre_topc @ X39 @ ( k6_tmap_1 @ X38 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X38 @ X37 ) ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('201',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X38 @ X37 ) ) ) )
      | ( v3_pre_topc @ X37 @ ( k6_tmap_1 @ X38 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['199','201'])).

thf('203',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['202','203','204','205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['198','209'])).

thf('211',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['191','210'])).

thf('212',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('213',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['140'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('214',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 )
        = ( k10_relat_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('215',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
          = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['212','215'])).

thf('217',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('218',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('220',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('221',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('222',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['163'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('226',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('227',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('228',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('229',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['227','228'])).

thf('230',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
          = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['226','229'])).

thf('231',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('232',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('234',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('235',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['163'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['225','237'])).

thf('239',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('242',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('243',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('244',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['140'])).

thf('245',plain,
    ( ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('247',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['242','247'])).

thf('249',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('250',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('251',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('252',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['248','249','250','251'])).

thf('253',plain,
    ( ( ( m1_subset_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['241','252'])).

thf('254',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('255',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['163'])).

thf('257',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 )
        = ( k10_relat_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['240','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['224','260'])).

thf('262',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('263',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('264',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relset_1 @ X5 @ X5 @ ( k6_partfun1 @ X5 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('266',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['263','266'])).

thf('268',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('269',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['267','268'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['235','236'])).

thf('271',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['269','270'])).

thf('272',plain,
    ( ( ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['262','271'])).

thf('273',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('274',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['211','261','274'])).

thf('276',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['155','164'])).

thf('277',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('278',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('279',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['171','277','278'])).

thf('280',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('281',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('282',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['280','281'])).

thf('283',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('284',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( ( k2_struct_0 @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('286',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( zip_tseitin_0 @ X0 @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ X0 @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['286'])).

thf('288',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['184','185'])).

thf('289',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('291',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['289','290'])).

thf('292',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['279','291'])).

thf('293',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['198','209'])).

thf('294',plain,
    ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('296',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('297',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('298',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['224','260'])).

thf('299',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['297','298'])).

thf('300',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('301',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('302',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('304',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['302','303'])).

thf('305',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('306',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['272','273'])).

thf('307',plain,
    ( ( ( k10_relat_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B )
      = sk_B )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['305','306'])).

thf('308',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295','296','304','307'])).

thf('309',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','308'])).

thf('310',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['135'])).

thf('311',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v5_pre_topc @ X0 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['133','311'])).

thf('313',plain,
    ( ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','312'])).

thf('314',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('315',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('316',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('317',plain,
    ( ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['159'])).

thf('318',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('319',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['317','318'])).

thf('320',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['309'])).

thf('321',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['319','320'])).

thf('322',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['316','321'])).

thf('323',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('324',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','323'])).

thf('325',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('326',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('327',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['325','326'])).

thf('328',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('329',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['327','328'])).

thf('330',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['324','329'])).

thf('331',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['316','321'])).

thf('332',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('333',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['331','332'])).

thf('334',plain,(
    ~ ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['330','333'])).

thf('335',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('336',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('337',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('338',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('339',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['335','336','337','338'])).

thf('340',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('341',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('342',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('343',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ( zip_tseitin_2 @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('345',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('346',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['343','344','345'])).

thf('347',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['340','346'])).

thf('348',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('349',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('350',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['347','348','349'])).

thf('351',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('352',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('353',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('354',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( ( k2_struct_0 @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('355',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
       != k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['353','354'])).

thf('356',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('357',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['355','356'])).

thf('358',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('360',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['350','351','352','358','359','360'])).

thf('362',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['339','361'])).

thf('363',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('364',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('365',plain,(
    v1_funct_1 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['363','364'])).

thf('366',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('367',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('368',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('369',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['95','322'])).

thf('370',plain,(
    v1_funct_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['366','367','368','369'])).

thf('371',plain,(
    zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['362','365','370'])).

thf('372',plain,(
    $false ),
    inference(demod,[status(thm)],['334','371'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qj21EfbVC5
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:02:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.94/7.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.94/7.17  % Solved by: fo/fo7.sh
% 6.94/7.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.94/7.17  % done 3748 iterations in 6.709s
% 6.94/7.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.94/7.17  % SZS output start Refutation
% 6.94/7.17  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.94/7.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.94/7.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 6.94/7.17  thf(sk_A_type, type, sk_A: $i).
% 6.94/7.17  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 6.94/7.17  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 6.94/7.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.94/7.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.94/7.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.94/7.17  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.94/7.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.94/7.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.94/7.17  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 6.94/7.17  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 6.94/7.17  thf(sk_B_type, type, sk_B: $i).
% 6.94/7.17  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 6.94/7.17  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 6.94/7.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.94/7.17  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 6.94/7.17  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 6.94/7.17  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 6.94/7.17  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.94/7.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.94/7.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.94/7.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.94/7.17  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 6.94/7.17  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 6.94/7.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.94/7.17  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 6.94/7.17  thf(d3_struct_0, axiom,
% 6.94/7.17    (![A:$i]:
% 6.94/7.17     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 6.94/7.17  thf('0', plain,
% 6.94/7.17      (![X6 : $i]:
% 6.94/7.17         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.17      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.17  thf(t113_tmap_1, conjecture,
% 6.94/7.17    (![A:$i]:
% 6.94/7.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.94/7.17       ( ![B:$i]:
% 6.94/7.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.94/7.17           ( ( v3_pre_topc @ B @ A ) <=>
% 6.94/7.17             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 6.94/7.17               ( v1_funct_2 @
% 6.94/7.17                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.94/7.17                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 6.94/7.17               ( v5_pre_topc @
% 6.94/7.17                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 6.94/7.17               ( m1_subset_1 @
% 6.94/7.17                 ( k7_tmap_1 @ A @ B ) @ 
% 6.94/7.17                 ( k1_zfmisc_1 @
% 6.94/7.17                   ( k2_zfmisc_1 @
% 6.94/7.17                     ( u1_struct_0 @ A ) @ 
% 6.94/7.17                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 6.94/7.17  thf(zf_stmt_0, negated_conjecture,
% 6.94/7.17    (~( ![A:$i]:
% 6.94/7.17        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.94/7.17            ( l1_pre_topc @ A ) ) =>
% 6.94/7.17          ( ![B:$i]:
% 6.94/7.17            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.94/7.17              ( ( v3_pre_topc @ B @ A ) <=>
% 6.94/7.17                ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 6.94/7.17                  ( v1_funct_2 @
% 6.94/7.17                    ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.94/7.17                    ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 6.94/7.17                  ( v5_pre_topc @
% 6.94/7.17                    ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 6.94/7.17                  ( m1_subset_1 @
% 6.94/7.17                    ( k7_tmap_1 @ A @ B ) @ 
% 6.94/7.17                    ( k1_zfmisc_1 @
% 6.94/7.17                      ( k2_zfmisc_1 @
% 6.94/7.17                        ( u1_struct_0 @ A ) @ 
% 6.94/7.17                        ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 6.94/7.17    inference('cnf.neg', [status(esa)], [t113_tmap_1])).
% 6.94/7.17  thf('1', plain,
% 6.94/7.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.17  thf(t104_tmap_1, axiom,
% 6.94/7.17    (![A:$i]:
% 6.94/7.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.94/7.17       ( ![B:$i]:
% 6.94/7.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.94/7.17           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 6.94/7.17             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 6.94/7.17  thf('2', plain,
% 6.94/7.17      (![X35 : $i, X36 : $i]:
% 6.94/7.17         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 6.94/7.17          | ((u1_struct_0 @ (k6_tmap_1 @ X36 @ X35)) = (u1_struct_0 @ X36))
% 6.94/7.17          | ~ (l1_pre_topc @ X36)
% 6.94/7.17          | ~ (v2_pre_topc @ X36)
% 6.94/7.17          | (v2_struct_0 @ X36))),
% 6.94/7.17      inference('cnf', [status(esa)], [t104_tmap_1])).
% 6.94/7.17  thf('3', plain,
% 6.94/7.17      (((v2_struct_0 @ sk_A)
% 6.94/7.17        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.17        | ~ (l1_pre_topc @ sk_A)
% 6.94/7.17        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 6.94/7.17      inference('sup-', [status(thm)], ['1', '2'])).
% 6.94/7.17  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.17  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.17  thf('6', plain,
% 6.94/7.17      (((v2_struct_0 @ sk_A)
% 6.94/7.17        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 6.94/7.17      inference('demod', [status(thm)], ['3', '4', '5'])).
% 6.94/7.17  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.17  thf('8', plain,
% 6.94/7.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.17      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.17  thf(t55_tops_2, axiom,
% 6.94/7.17    (![A:$i]:
% 6.94/7.17     ( ( l1_pre_topc @ A ) =>
% 6.94/7.17       ( ![B:$i]:
% 6.94/7.17         ( ( l1_pre_topc @ B ) =>
% 6.94/7.17           ( ![C:$i]:
% 6.94/7.17             ( ( ( m1_subset_1 @
% 6.94/7.17                   C @ 
% 6.94/7.17                   ( k1_zfmisc_1 @
% 6.94/7.17                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 6.94/7.17                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.94/7.17                 ( v1_funct_1 @ C ) ) =>
% 6.94/7.17               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 6.94/7.17                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 6.94/7.17                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 6.94/7.17                   ( ![D:$i]:
% 6.94/7.17                     ( ( m1_subset_1 @
% 6.94/7.17                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.94/7.17                       ( ( v3_pre_topc @ D @ B ) =>
% 6.94/7.17                         ( v3_pre_topc @
% 6.94/7.17                           ( k8_relset_1 @
% 6.94/7.17                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 6.94/7.17                           A ) ) ) ) ) ) ) ) ) ) ))).
% 6.94/7.17  thf(zf_stmt_1, axiom,
% 6.94/7.17    (![D:$i,C:$i,B:$i,A:$i]:
% 6.94/7.17     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 6.94/7.17       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.94/7.17         ( ( v3_pre_topc @ D @ B ) =>
% 6.94/7.17           ( v3_pre_topc @
% 6.94/7.17             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 6.94/7.17             A ) ) ) ))).
% 6.94/7.17  thf('9', plain,
% 6.94/7.17      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 6.94/7.17         ((zip_tseitin_1 @ X16 @ X19 @ X17 @ X20)
% 6.94/7.17          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 6.94/7.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.94/7.17  thf(t171_funct_2, axiom,
% 6.94/7.17    (![A:$i,B:$i]:
% 6.94/7.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.94/7.17       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 6.94/7.17  thf('10', plain,
% 6.94/7.17      (![X4 : $i, X5 : $i]:
% 6.94/7.17         (((k8_relset_1 @ X5 @ X5 @ (k6_partfun1 @ X5) @ X4) = (X4))
% 6.94/7.17          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 6.94/7.17      inference('cnf', [status(esa)], [t171_funct_2])).
% 6.94/7.17  thf('11', plain,
% 6.94/7.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.94/7.17         ((zip_tseitin_1 @ X1 @ X3 @ X0 @ X2)
% 6.94/7.17          | ((k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 6.94/7.17              (k6_partfun1 @ (u1_struct_0 @ X0)) @ X1) = (X1)))),
% 6.94/7.17      inference('sup-', [status(thm)], ['9', '10'])).
% 6.94/7.17  thf('12', plain,
% 6.94/7.17      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 6.94/7.17         ((zip_tseitin_1 @ X16 @ X19 @ X17 @ X20)
% 6.94/7.17          | ~ (v3_pre_topc @ 
% 6.94/7.17               (k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X17) @ 
% 6.94/7.17                X19 @ X16) @ 
% 6.94/7.17               X20))),
% 6.94/7.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.94/7.17  thf('13', plain,
% 6.94/7.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.94/7.17         (~ (v3_pre_topc @ X0 @ X1)
% 6.94/7.17          | (zip_tseitin_1 @ X0 @ X3 @ X1 @ X2)
% 6.94/7.17          | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ X1)) @ X1 @ X1))),
% 6.94/7.17      inference('sup-', [status(thm)], ['11', '12'])).
% 6.94/7.17  thf('14', plain,
% 6.94/7.17      (![X0 : $i, X1 : $i]:
% 6.94/7.17         (~ (v3_pre_topc @ X1 @ X0)
% 6.94/7.17          | (zip_tseitin_1 @ X1 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 6.94/7.17      inference('condensation', [status(thm)], ['13'])).
% 6.94/7.17  thf('15', plain,
% 6.94/7.17      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 6.94/7.17         ((zip_tseitin_1 @ X16 @ X19 @ X17 @ X20) | (v3_pre_topc @ X16 @ X17))),
% 6.94/7.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.94/7.17  thf('16', plain,
% 6.94/7.17      (![X0 : $i, X1 : $i]:
% 6.94/7.17         (zip_tseitin_1 @ X1 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)),
% 6.94/7.17      inference('clc', [status(thm)], ['14', '15'])).
% 6.94/7.17  thf(zf_stmt_2, axiom,
% 6.94/7.17    (![C:$i,B:$i,A:$i]:
% 6.94/7.17     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 6.94/7.17       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 6.94/7.17         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 6.94/7.17  thf('17', plain,
% 6.94/7.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.94/7.17         (~ (zip_tseitin_1 @ (sk_D @ X21 @ X22 @ X23) @ X23 @ X22 @ X21)
% 6.94/7.17          | (v5_pre_topc @ X23 @ X21 @ X22)
% 6.94/7.17          | ~ (zip_tseitin_2 @ X23 @ X22 @ X21))),
% 6.94/7.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.94/7.17  thf('18', plain,
% 6.94/7.17      (![X0 : $i]:
% 6.94/7.17         (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)
% 6.94/7.17          | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 6.94/7.17      inference('sup-', [status(thm)], ['16', '17'])).
% 6.94/7.17  thf('19', plain,
% 6.94/7.17      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.17           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.17        | (v5_pre_topc @ 
% 6.94/7.17           (k6_partfun1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))) @ 
% 6.94/7.17           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.17      inference('sup-', [status(thm)], ['8', '18'])).
% 6.94/7.17  thf('20', plain,
% 6.94/7.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.17      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.17  thf('21', plain,
% 6.94/7.17      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.17           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('demod', [status(thm)], ['19', '20'])).
% 6.94/7.18  thf('22', plain,
% 6.94/7.18      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (l1_struct_0 @ sk_A)
% 6.94/7.18        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['0', '21'])).
% 6.94/7.18  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf(dt_l1_pre_topc, axiom,
% 6.94/7.18    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 6.94/7.18  thf('24', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 6.94/7.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 6.94/7.18  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('26', plain,
% 6.94/7.18      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('demod', [status(thm)], ['22', '25'])).
% 6.94/7.18  thf('27', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf(dt_k7_tmap_1, axiom,
% 6.94/7.18    (![A:$i,B:$i]:
% 6.94/7.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.94/7.18         ( l1_pre_topc @ A ) & 
% 6.94/7.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.94/7.18       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 6.94/7.18         ( v1_funct_2 @
% 6.94/7.18           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.94/7.18           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 6.94/7.18         ( m1_subset_1 @
% 6.94/7.18           ( k7_tmap_1 @ A @ B ) @ 
% 6.94/7.18           ( k1_zfmisc_1 @
% 6.94/7.18             ( k2_zfmisc_1 @
% 6.94/7.18               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 6.94/7.18  thf('28', plain,
% 6.94/7.18      (![X32 : $i, X33 : $i]:
% 6.94/7.18         (~ (l1_pre_topc @ X32)
% 6.94/7.18          | ~ (v2_pre_topc @ X32)
% 6.94/7.18          | (v2_struct_0 @ X32)
% 6.94/7.18          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 6.94/7.18          | (m1_subset_1 @ (k7_tmap_1 @ X32 @ X33) @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ 
% 6.94/7.18               (u1_struct_0 @ (k6_tmap_1 @ X32 @ X33))))))),
% 6.94/7.18      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 6.94/7.18  thf('29', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 6.94/7.18        | (v2_struct_0 @ sk_A)
% 6.94/7.18        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18        | ~ (l1_pre_topc @ sk_A))),
% 6.94/7.18      inference('sup-', [status(thm)], ['27', '28'])).
% 6.94/7.18  thf('30', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf(d10_tmap_1, axiom,
% 6.94/7.18    (![A:$i]:
% 6.94/7.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.94/7.18       ( ![B:$i]:
% 6.94/7.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.94/7.18           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 6.94/7.18  thf('31', plain,
% 6.94/7.18      (![X28 : $i, X29 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 6.94/7.18          | ((k7_tmap_1 @ X29 @ X28) = (k6_partfun1 @ (u1_struct_0 @ X29)))
% 6.94/7.18          | ~ (l1_pre_topc @ X29)
% 6.94/7.18          | ~ (v2_pre_topc @ X29)
% 6.94/7.18          | (v2_struct_0 @ X29))),
% 6.94/7.18      inference('cnf', [status(esa)], [d10_tmap_1])).
% 6.94/7.18  thf('32', plain,
% 6.94/7.18      (((v2_struct_0 @ sk_A)
% 6.94/7.18        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18        | ~ (l1_pre_topc @ sk_A)
% 6.94/7.18        | ((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['30', '31'])).
% 6.94/7.18  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('35', plain,
% 6.94/7.18      (((v2_struct_0 @ sk_A)
% 6.94/7.18        | ((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 6.94/7.18      inference('demod', [status(thm)], ['32', '33', '34'])).
% 6.94/7.18  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('37', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('38', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('41', plain,
% 6.94/7.18      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18        | (v2_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['29', '37', '38', '39', '40'])).
% 6.94/7.18  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('43', plain,
% 6.94/7.18      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (k1_zfmisc_1 @ 
% 6.94/7.18         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 6.94/7.18      inference('clc', [status(thm)], ['41', '42'])).
% 6.94/7.18  thf(zf_stmt_3, axiom,
% 6.94/7.18    (![B:$i,A:$i]:
% 6.94/7.18     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 6.94/7.18         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 6.94/7.18       ( zip_tseitin_0 @ B @ A ) ))).
% 6.94/7.18  thf('44', plain,
% 6.94/7.18      (![X14 : $i, X15 : $i]:
% 6.94/7.18         ((zip_tseitin_0 @ X14 @ X15) | ((k2_struct_0 @ X14) = (k1_xboole_0)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.94/7.18  thf('45', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('46', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 6.94/7.18  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 6.94/7.18  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 6.94/7.18  thf(zf_stmt_7, axiom,
% 6.94/7.18    (![A:$i]:
% 6.94/7.18     ( ( l1_pre_topc @ A ) =>
% 6.94/7.18       ( ![B:$i]:
% 6.94/7.18         ( ( l1_pre_topc @ B ) =>
% 6.94/7.18           ( ![C:$i]:
% 6.94/7.18             ( ( ( v1_funct_1 @ C ) & 
% 6.94/7.18                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.94/7.18                 ( m1_subset_1 @
% 6.94/7.18                   C @ 
% 6.94/7.18                   ( k1_zfmisc_1 @
% 6.94/7.18                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.94/7.18               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 6.94/7.18  thf('47', plain,
% 6.94/7.18      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.94/7.18         (~ (l1_pre_topc @ X25)
% 6.94/7.18          | ~ (zip_tseitin_0 @ X25 @ X26)
% 6.94/7.18          | (zip_tseitin_2 @ X27 @ X25 @ X26)
% 6.94/7.18          | ~ (m1_subset_1 @ X27 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 6.94/7.18          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 6.94/7.18          | ~ (v1_funct_1 @ X27)
% 6.94/7.18          | ~ (l1_pre_topc @ X26))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_7])).
% 6.94/7.18  thf('48', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X1 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 6.94/7.18          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (v1_funct_1 @ X1)
% 6.94/7.18          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 6.94/7.18               (u1_struct_0 @ X0))
% 6.94/7.18          | (zip_tseitin_2 @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (l1_pre_topc @ X0))),
% 6.94/7.18      inference('sup-', [status(thm)], ['46', '47'])).
% 6.94/7.18  thf('49', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf(dt_k6_tmap_1, axiom,
% 6.94/7.18    (![A:$i,B:$i]:
% 6.94/7.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.94/7.18         ( l1_pre_topc @ A ) & 
% 6.94/7.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.94/7.18       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 6.94/7.18         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 6.94/7.18         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 6.94/7.18  thf('50', plain,
% 6.94/7.18      (![X30 : $i, X31 : $i]:
% 6.94/7.18         (~ (l1_pre_topc @ X30)
% 6.94/7.18          | ~ (v2_pre_topc @ X30)
% 6.94/7.18          | (v2_struct_0 @ X30)
% 6.94/7.18          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 6.94/7.18          | (l1_pre_topc @ (k6_tmap_1 @ X30 @ X31)))),
% 6.94/7.18      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 6.94/7.18  thf('51', plain,
% 6.94/7.18      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v2_struct_0 @ sk_A)
% 6.94/7.18        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18        | ~ (l1_pre_topc @ sk_A))),
% 6.94/7.18      inference('sup-', [status(thm)], ['49', '50'])).
% 6.94/7.18  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('54', plain,
% 6.94/7.18      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['51', '52', '53'])).
% 6.94/7.18  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('56', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['54', '55'])).
% 6.94/7.18  thf('57', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('58', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X1 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 6.94/7.18          | ~ (v1_funct_1 @ X1)
% 6.94/7.18          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 6.94/7.18          | (zip_tseitin_2 @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (l1_pre_topc @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['48', '56', '57'])).
% 6.94/7.18  thf('59', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18          | ~ (v1_funct_1 @ X0))),
% 6.94/7.18      inference('sup-', [status(thm)], ['45', '58'])).
% 6.94/7.18  thf('60', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['54', '55'])).
% 6.94/7.18  thf('61', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('62', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18          | ~ (v1_funct_1 @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['59', '60', '61'])).
% 6.94/7.18  thf('63', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 6.94/7.18          | ~ (v1_funct_1 @ X0)
% 6.94/7.18          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (m1_subset_1 @ X0 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['44', '62'])).
% 6.94/7.18  thf('64', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('65', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('66', plain,
% 6.94/7.18      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 6.94/7.18        | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('sup+', [status(thm)], ['64', '65'])).
% 6.94/7.18  thf('67', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['54', '55'])).
% 6.94/7.18  thf('68', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 6.94/7.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 6.94/7.18  thf('69', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('sup-', [status(thm)], ['67', '68'])).
% 6.94/7.18  thf('70', plain,
% 6.94/7.18      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['66', '69'])).
% 6.94/7.18  thf('71', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 6.94/7.18          | ~ (v1_funct_1 @ X0)
% 6.94/7.18          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (m1_subset_1 @ X0 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 6.94/7.18      inference('demod', [status(thm)], ['63', '70'])).
% 6.94/7.18  thf('72', plain,
% 6.94/7.18      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 6.94/7.18        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['43', '71'])).
% 6.94/7.18  thf('73', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('74', plain,
% 6.94/7.18      (![X32 : $i, X33 : $i]:
% 6.94/7.18         (~ (l1_pre_topc @ X32)
% 6.94/7.18          | ~ (v2_pre_topc @ X32)
% 6.94/7.18          | (v2_struct_0 @ X32)
% 6.94/7.18          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 6.94/7.18          | (v1_funct_2 @ (k7_tmap_1 @ X32 @ X33) @ (u1_struct_0 @ X32) @ 
% 6.94/7.18             (u1_struct_0 @ (k6_tmap_1 @ X32 @ X33))))),
% 6.94/7.18      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 6.94/7.18  thf('75', plain,
% 6.94/7.18      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18        | (v2_struct_0 @ sk_A)
% 6.94/7.18        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18        | ~ (l1_pre_topc @ sk_A))),
% 6.94/7.18      inference('sup-', [status(thm)], ['73', '74'])).
% 6.94/7.18  thf('76', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('77', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('80', plain,
% 6.94/7.18      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18        | (v2_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 6.94/7.18  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('82', plain,
% 6.94/7.18      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['80', '81'])).
% 6.94/7.18  thf('83', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('84', plain,
% 6.94/7.18      (![X32 : $i, X33 : $i]:
% 6.94/7.18         (~ (l1_pre_topc @ X32)
% 6.94/7.18          | ~ (v2_pre_topc @ X32)
% 6.94/7.18          | (v2_struct_0 @ X32)
% 6.94/7.18          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 6.94/7.18          | (v1_funct_1 @ (k7_tmap_1 @ X32 @ X33)))),
% 6.94/7.18      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 6.94/7.18  thf('85', plain,
% 6.94/7.18      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v2_struct_0 @ sk_A)
% 6.94/7.18        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18        | ~ (l1_pre_topc @ sk_A))),
% 6.94/7.18      inference('sup-', [status(thm)], ['83', '84'])).
% 6.94/7.18  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('88', plain,
% 6.94/7.18      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['85', '86', '87'])).
% 6.94/7.18  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('90', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['88', '89'])).
% 6.94/7.18  thf('91', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('92', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('demod', [status(thm)], ['90', '91'])).
% 6.94/7.18  thf('93', plain,
% 6.94/7.18      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 6.94/7.18      inference('demod', [status(thm)], ['72', '82', '92'])).
% 6.94/7.18  thf('94', plain,
% 6.94/7.18      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('demod', [status(thm)], ['19', '20'])).
% 6.94/7.18  thf('95', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 6.94/7.18        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['93', '94'])).
% 6.94/7.18  thf('96', plain,
% 6.94/7.18      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (k1_zfmisc_1 @ 
% 6.94/7.18         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 6.94/7.18      inference('clc', [status(thm)], ['41', '42'])).
% 6.94/7.18  thf('97', plain,
% 6.94/7.18      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('98', plain,
% 6.94/7.18      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.94/7.18      inference('split', [status(esa)], ['97'])).
% 6.94/7.18  thf('99', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf(t106_tmap_1, axiom,
% 6.94/7.18    (![A:$i]:
% 6.94/7.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.94/7.18       ( ![B:$i]:
% 6.94/7.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.94/7.18           ( ( v3_pre_topc @ B @ A ) <=>
% 6.94/7.18             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 6.94/7.18               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 6.94/7.18  thf('100', plain,
% 6.94/7.18      (![X40 : $i, X41 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 6.94/7.18          | ~ (v3_pre_topc @ X40 @ X41)
% 6.94/7.18          | ((g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))
% 6.94/7.18              = (k6_tmap_1 @ X41 @ X40))
% 6.94/7.18          | ~ (l1_pre_topc @ X41)
% 6.94/7.18          | ~ (v2_pre_topc @ X41)
% 6.94/7.18          | (v2_struct_0 @ X41))),
% 6.94/7.18      inference('cnf', [status(esa)], [t106_tmap_1])).
% 6.94/7.18  thf('101', plain,
% 6.94/7.18      (((v2_struct_0 @ sk_A)
% 6.94/7.18        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18        | ~ (l1_pre_topc @ sk_A)
% 6.94/7.18        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 6.94/7.18            = (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('sup-', [status(thm)], ['99', '100'])).
% 6.94/7.18  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('104', plain,
% 6.94/7.18      (((v2_struct_0 @ sk_A)
% 6.94/7.18        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 6.94/7.18            = (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['101', '102', '103'])).
% 6.94/7.18  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('106', plain,
% 6.94/7.18      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 6.94/7.18        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 6.94/7.18            = (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('clc', [status(thm)], ['104', '105'])).
% 6.94/7.18  thf('107', plain,
% 6.94/7.18      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 6.94/7.18          = (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['98', '106'])).
% 6.94/7.18  thf('108', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf(t62_pre_topc, axiom,
% 6.94/7.18    (![A:$i]:
% 6.94/7.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.94/7.18       ( ![B:$i]:
% 6.94/7.18         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 6.94/7.18           ( ![C:$i]:
% 6.94/7.18             ( ( ( v1_funct_1 @ C ) & 
% 6.94/7.18                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.94/7.18                 ( m1_subset_1 @
% 6.94/7.18                   C @ 
% 6.94/7.18                   ( k1_zfmisc_1 @
% 6.94/7.18                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.94/7.18               ( ![D:$i]:
% 6.94/7.18                 ( ( ( v1_funct_1 @ D ) & 
% 6.94/7.18                     ( v1_funct_2 @
% 6.94/7.18                       D @ 
% 6.94/7.18                       ( u1_struct_0 @
% 6.94/7.18                         ( g1_pre_topc @
% 6.94/7.18                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 6.94/7.18                       ( u1_struct_0 @ B ) ) & 
% 6.94/7.18                     ( m1_subset_1 @
% 6.94/7.18                       D @ 
% 6.94/7.18                       ( k1_zfmisc_1 @
% 6.94/7.18                         ( k2_zfmisc_1 @
% 6.94/7.18                           ( u1_struct_0 @
% 6.94/7.18                             ( g1_pre_topc @
% 6.94/7.18                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 6.94/7.18                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.94/7.18                   ( ( ( C ) = ( D ) ) =>
% 6.94/7.18                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 6.94/7.18                       ( v5_pre_topc @
% 6.94/7.18                         D @ 
% 6.94/7.18                         ( g1_pre_topc @
% 6.94/7.18                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 6.94/7.18                         B ) ) ) ) ) ) ) ) ) ))).
% 6.94/7.18  thf('109', plain,
% 6.94/7.18      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.94/7.18         (~ (v2_pre_topc @ X10)
% 6.94/7.18          | ~ (l1_pre_topc @ X10)
% 6.94/7.18          | ~ (v1_funct_1 @ X11)
% 6.94/7.18          | ~ (v1_funct_2 @ X11 @ 
% 6.94/7.18               (u1_struct_0 @ 
% 6.94/7.18                (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12))) @ 
% 6.94/7.18               (u1_struct_0 @ X10))
% 6.94/7.18          | ~ (m1_subset_1 @ X11 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ 
% 6.94/7.18                 (u1_struct_0 @ 
% 6.94/7.18                  (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12))) @ 
% 6.94/7.18                 (u1_struct_0 @ X10))))
% 6.94/7.18          | ~ (v5_pre_topc @ X11 @ 
% 6.94/7.18               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)) @ X10)
% 6.94/7.18          | (v5_pre_topc @ X13 @ X12 @ X10)
% 6.94/7.18          | ((X13) != (X11))
% 6.94/7.18          | ~ (m1_subset_1 @ X13 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 6.94/7.18          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 6.94/7.18          | ~ (v1_funct_1 @ X13)
% 6.94/7.18          | ~ (l1_pre_topc @ X12)
% 6.94/7.18          | ~ (v2_pre_topc @ X12))),
% 6.94/7.18      inference('cnf', [status(esa)], [t62_pre_topc])).
% 6.94/7.18  thf('110', plain,
% 6.94/7.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.94/7.18         (~ (v2_pre_topc @ X12)
% 6.94/7.18          | ~ (l1_pre_topc @ X12)
% 6.94/7.18          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 6.94/7.18          | ~ (m1_subset_1 @ X11 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 6.94/7.18          | (v5_pre_topc @ X11 @ X12 @ X10)
% 6.94/7.18          | ~ (v5_pre_topc @ X11 @ 
% 6.94/7.18               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)) @ X10)
% 6.94/7.18          | ~ (m1_subset_1 @ X11 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ 
% 6.94/7.18                 (u1_struct_0 @ 
% 6.94/7.18                  (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12))) @ 
% 6.94/7.18                 (u1_struct_0 @ X10))))
% 6.94/7.18          | ~ (v1_funct_2 @ X11 @ 
% 6.94/7.18               (u1_struct_0 @ 
% 6.94/7.18                (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12))) @ 
% 6.94/7.18               (u1_struct_0 @ X10))
% 6.94/7.18          | ~ (v1_funct_1 @ X11)
% 6.94/7.18          | ~ (l1_pre_topc @ X10)
% 6.94/7.18          | ~ (v2_pre_topc @ X10))),
% 6.94/7.18      inference('simplify', [status(thm)], ['109'])).
% 6.94/7.18  thf('111', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X1 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ 
% 6.94/7.18               (u1_struct_0 @ 
% 6.94/7.18                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 6.94/7.18               (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (v1_funct_1 @ X1)
% 6.94/7.18          | ~ (v1_funct_2 @ X1 @ 
% 6.94/7.18               (u1_struct_0 @ 
% 6.94/7.18                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 6.94/7.18               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18          | ~ (v5_pre_topc @ X1 @ 
% 6.94/7.18               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (m1_subset_1 @ X1 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 6.94/7.18          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ 
% 6.94/7.18               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18          | ~ (l1_pre_topc @ X0)
% 6.94/7.18          | ~ (v2_pre_topc @ X0))),
% 6.94/7.18      inference('sup-', [status(thm)], ['108', '110'])).
% 6.94/7.18  thf('112', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('113', plain,
% 6.94/7.18      (![X30 : $i, X31 : $i]:
% 6.94/7.18         (~ (l1_pre_topc @ X30)
% 6.94/7.18          | ~ (v2_pre_topc @ X30)
% 6.94/7.18          | (v2_struct_0 @ X30)
% 6.94/7.18          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 6.94/7.18          | (v2_pre_topc @ (k6_tmap_1 @ X30 @ X31)))),
% 6.94/7.18      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 6.94/7.18  thf('114', plain,
% 6.94/7.18      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v2_struct_0 @ sk_A)
% 6.94/7.18        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18        | ~ (l1_pre_topc @ sk_A))),
% 6.94/7.18      inference('sup-', [status(thm)], ['112', '113'])).
% 6.94/7.18  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('117', plain,
% 6.94/7.18      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['114', '115', '116'])).
% 6.94/7.18  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('119', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['117', '118'])).
% 6.94/7.18  thf('120', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['54', '55'])).
% 6.94/7.18  thf('121', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('122', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('123', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('124', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X1 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ 
% 6.94/7.18               (u1_struct_0 @ 
% 6.94/7.18                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 6.94/7.18               (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (v1_funct_1 @ X1)
% 6.94/7.18          | ~ (v1_funct_2 @ X1 @ 
% 6.94/7.18               (u1_struct_0 @ 
% 6.94/7.18                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 6.94/7.18               (u1_struct_0 @ sk_A))
% 6.94/7.18          | ~ (v5_pre_topc @ X1 @ 
% 6.94/7.18               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (m1_subset_1 @ X1 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.94/7.18          | ~ (l1_pre_topc @ X0)
% 6.94/7.18          | ~ (v2_pre_topc @ X0))),
% 6.94/7.18      inference('demod', [status(thm)],
% 6.94/7.18                ['111', '119', '120', '121', '122', '123'])).
% 6.94/7.18  thf('125', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (~ (m1_subset_1 @ X0 @ 
% 6.94/7.18              (k1_zfmisc_1 @ 
% 6.94/7.18               (k2_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 6.94/7.18                (u1_struct_0 @ sk_A))))
% 6.94/7.18           | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18           | ~ (l1_pre_topc @ sk_A)
% 6.94/7.18           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18           | ~ (m1_subset_1 @ X0 @ 
% 6.94/7.18                (k1_zfmisc_1 @ 
% 6.94/7.18                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18           | ~ (v5_pre_topc @ X0 @ 
% 6.94/7.18                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 6.94/7.18                (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18           | ~ (v1_funct_2 @ X0 @ 
% 6.94/7.18                (u1_struct_0 @ 
% 6.94/7.18                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 6.94/7.18                (u1_struct_0 @ sk_A))
% 6.94/7.18           | ~ (v1_funct_1 @ X0)))
% 6.94/7.18         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['107', '124'])).
% 6.94/7.18  thf('126', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('129', plain,
% 6.94/7.18      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 6.94/7.18          = (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['98', '106'])).
% 6.94/7.18  thf('130', plain,
% 6.94/7.18      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 6.94/7.18          = (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['98', '106'])).
% 6.94/7.18  thf('131', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('132', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (~ (m1_subset_1 @ X0 @ 
% 6.94/7.18              (k1_zfmisc_1 @ 
% 6.94/7.18               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18           | ~ (m1_subset_1 @ X0 @ 
% 6.94/7.18                (k1_zfmisc_1 @ 
% 6.94/7.18                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18           | ~ (v5_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18                (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18           | ~ (v1_funct_1 @ X0)))
% 6.94/7.18         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.94/7.18      inference('demod', [status(thm)],
% 6.94/7.18                ['125', '126', '127', '128', '129', '130', '131'])).
% 6.94/7.18  thf('133', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (~ (v1_funct_1 @ X0)
% 6.94/7.18           | ~ (v5_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18                (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18           | ~ (m1_subset_1 @ X0 @ 
% 6.94/7.18                (k1_zfmisc_1 @ 
% 6.94/7.18                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))))
% 6.94/7.18         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.94/7.18      inference('simplify', [status(thm)], ['132'])).
% 6.94/7.18  thf('134', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('135', plain,
% 6.94/7.18      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('136', plain,
% 6.94/7.18      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('split', [status(esa)], ['135'])).
% 6.94/7.18  thf('137', plain,
% 6.94/7.18      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['134', '136'])).
% 6.94/7.18  thf('138', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('139', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('140', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 6.94/7.18        | (v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('141', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('split', [status(esa)], ['140'])).
% 6.94/7.18  thf('142', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['139', '141'])).
% 6.94/7.18  thf('143', plain,
% 6.94/7.18      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['138', '142'])).
% 6.94/7.18  thf('144', plain,
% 6.94/7.18      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18           (k1_zfmisc_1 @ 
% 6.94/7.18            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 6.94/7.18        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('145', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('146', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('147', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('148', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('149', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('150', plain,
% 6.94/7.18      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['80', '81'])).
% 6.94/7.18  thf('151', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('152', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('demod', [status(thm)], ['90', '91'])).
% 6.94/7.18  thf('153', plain,
% 6.94/7.18      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k1_zfmisc_1 @ 
% 6.94/7.18            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)],
% 6.94/7.18                ['144', '145', '146', '147', '148', '149', '150', '151', '152'])).
% 6.94/7.18  thf('154', plain,
% 6.94/7.18      (((~ (v3_pre_topc @ sk_B @ sk_A)
% 6.94/7.18         | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['143', '153'])).
% 6.94/7.18  thf('155', plain,
% 6.94/7.18      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))) & 
% 6.94/7.18             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['137', '154'])).
% 6.94/7.18  thf('156', plain,
% 6.94/7.18      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (k1_zfmisc_1 @ 
% 6.94/7.18         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 6.94/7.18      inference('clc', [status(thm)], ['41', '42'])).
% 6.94/7.18  thf('157', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('158', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('159', plain,
% 6.94/7.18      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18           (k1_zfmisc_1 @ 
% 6.94/7.18            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 6.94/7.18        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('160', plain,
% 6.94/7.18      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18           (k1_zfmisc_1 @ 
% 6.94/7.18            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 6.94/7.18         <= (~
% 6.94/7.18             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('split', [status(esa)], ['159'])).
% 6.94/7.18  thf('161', plain,
% 6.94/7.18      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18           (k1_zfmisc_1 @ 
% 6.94/7.18            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 6.94/7.18         <= (~
% 6.94/7.18             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['158', '160'])).
% 6.94/7.18  thf('162', plain,
% 6.94/7.18      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k1_zfmisc_1 @ 
% 6.94/7.18            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 6.94/7.18         <= (~
% 6.94/7.18             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['157', '161'])).
% 6.94/7.18  thf('163', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['156', '162'])).
% 6.94/7.18  thf('164', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 6.94/7.18      inference('sat_resolution*', [status(thm)], ['163'])).
% 6.94/7.18  thf('165', plain,
% 6.94/7.18      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['155', '164'])).
% 6.94/7.18  thf('166', plain,
% 6.94/7.18      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('split', [status(esa)], ['135'])).
% 6.94/7.18  thf('167', plain,
% 6.94/7.18      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 6.94/7.18         (~ (v5_pre_topc @ X23 @ X21 @ X22)
% 6.94/7.18          | (zip_tseitin_1 @ X24 @ X23 @ X22 @ X21)
% 6.94/7.18          | ~ (zip_tseitin_2 @ X23 @ X22 @ X21))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.94/7.18  thf('168', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (~ (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18           | (zip_tseitin_1 @ X0 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['166', '167'])).
% 6.94/7.18  thf('169', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('170', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('171', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['168', '169', '170'])).
% 6.94/7.18  thf('172', plain,
% 6.94/7.18      (![X14 : $i, X15 : $i]:
% 6.94/7.18         ((zip_tseitin_0 @ X14 @ X15) | ((k2_struct_0 @ X14) = (k1_xboole_0)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.94/7.18  thf('173', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('split', [status(esa)], ['140'])).
% 6.94/7.18  thf('174', plain,
% 6.94/7.18      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.94/7.18         (~ (l1_pre_topc @ X25)
% 6.94/7.18          | ~ (zip_tseitin_0 @ X25 @ X26)
% 6.94/7.18          | (zip_tseitin_2 @ X27 @ X25 @ X26)
% 6.94/7.18          | ~ (m1_subset_1 @ X27 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 6.94/7.18          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 6.94/7.18          | ~ (v1_funct_1 @ X27)
% 6.94/7.18          | ~ (l1_pre_topc @ X26))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_7])).
% 6.94/7.18  thf('175', plain,
% 6.94/7.18      (((~ (l1_pre_topc @ sk_A)
% 6.94/7.18         | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18         | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18              (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         | (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18            (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18         | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['173', '174'])).
% 6.94/7.18  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('177', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['88', '89'])).
% 6.94/7.18  thf('178', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('179', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['54', '55'])).
% 6.94/7.18  thf('180', plain,
% 6.94/7.18      (((~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (u1_struct_0 @ sk_A))
% 6.94/7.18         | (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18            (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['175', '176', '177', '178', '179'])).
% 6.94/7.18  thf('181', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('182', plain,
% 6.94/7.18      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['80', '81'])).
% 6.94/7.18  thf('183', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('184', plain,
% 6.94/7.18      ((((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18          (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 6.94/7.18  thf('185', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 6.94/7.18      inference('sat_resolution*', [status(thm)], ['163'])).
% 6.94/7.18  thf('186', plain,
% 6.94/7.18      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18        | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['184', '185'])).
% 6.94/7.18  thf('187', plain,
% 6.94/7.18      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 6.94/7.18        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 6.94/7.18      inference('sup-', [status(thm)], ['172', '186'])).
% 6.94/7.18  thf('188', plain,
% 6.94/7.18      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['66', '69'])).
% 6.94/7.18  thf('189', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 6.94/7.18        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['187', '188'])).
% 6.94/7.18  thf('190', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['168', '169', '170'])).
% 6.94/7.18  thf('191', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 6.94/7.18           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['189', '190'])).
% 6.94/7.18  thf('192', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('193', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('194', plain,
% 6.94/7.18      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 6.94/7.18          | (v3_pre_topc @ 
% 6.94/7.18             (k8_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19 @ 
% 6.94/7.18              X16) @ 
% 6.94/7.18             X18)
% 6.94/7.18          | ~ (v3_pre_topc @ X16 @ X17)
% 6.94/7.18          | ~ (zip_tseitin_1 @ X16 @ X19 @ X17 @ X18))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.94/7.18  thf('195', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.94/7.18          | ~ (zip_tseitin_1 @ X0 @ X2 @ (k6_tmap_1 @ sk_A @ sk_B) @ X1)
% 6.94/7.18          | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (v3_pre_topc @ 
% 6.94/7.18             (k8_relset_1 @ (u1_struct_0 @ X1) @ 
% 6.94/7.18              (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ X2 @ X0) @ 
% 6.94/7.18             X1))),
% 6.94/7.18      inference('sup-', [status(thm)], ['193', '194'])).
% 6.94/7.18  thf('196', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('197', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.94/7.18          | ~ (zip_tseitin_1 @ X0 @ X2 @ (k6_tmap_1 @ sk_A @ sk_B) @ X1)
% 6.94/7.18          | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (v3_pre_topc @ 
% 6.94/7.18             (k8_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_A) @ X2 @ X0) @ 
% 6.94/7.18             X1))),
% 6.94/7.18      inference('demod', [status(thm)], ['195', '196'])).
% 6.94/7.18  thf('198', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         ((v3_pre_topc @ 
% 6.94/7.18           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 6.94/7.18           X0)
% 6.94/7.18          | ~ (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 6.94/7.18      inference('sup-', [status(thm)], ['192', '197'])).
% 6.94/7.18  thf('199', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf(t105_tmap_1, axiom,
% 6.94/7.18    (![A:$i]:
% 6.94/7.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.94/7.18       ( ![B:$i]:
% 6.94/7.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.94/7.18           ( ![C:$i]:
% 6.94/7.18             ( ( m1_subset_1 @
% 6.94/7.18                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 6.94/7.18               ( ( ( C ) = ( B ) ) =>
% 6.94/7.18                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 6.94/7.18  thf('200', plain,
% 6.94/7.18      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.94/7.18          | ((X39) != (X37))
% 6.94/7.18          | (v3_pre_topc @ X39 @ (k6_tmap_1 @ X38 @ X37))
% 6.94/7.18          | ~ (m1_subset_1 @ X39 @ 
% 6.94/7.18               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X38 @ X37))))
% 6.94/7.18          | ~ (l1_pre_topc @ X38)
% 6.94/7.18          | ~ (v2_pre_topc @ X38)
% 6.94/7.18          | (v2_struct_0 @ X38))),
% 6.94/7.18      inference('cnf', [status(esa)], [t105_tmap_1])).
% 6.94/7.18  thf('201', plain,
% 6.94/7.18      (![X37 : $i, X38 : $i]:
% 6.94/7.18         ((v2_struct_0 @ X38)
% 6.94/7.18          | ~ (v2_pre_topc @ X38)
% 6.94/7.18          | ~ (l1_pre_topc @ X38)
% 6.94/7.18          | ~ (m1_subset_1 @ X37 @ 
% 6.94/7.18               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X38 @ X37))))
% 6.94/7.18          | (v3_pre_topc @ X37 @ (k6_tmap_1 @ X38 @ X37))
% 6.94/7.18          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38))))),
% 6.94/7.18      inference('simplify', [status(thm)], ['200'])).
% 6.94/7.18  thf('202', plain,
% 6.94/7.18      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.94/7.18        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.94/7.18        | (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (l1_pre_topc @ sk_A)
% 6.94/7.18        | ~ (v2_pre_topc @ sk_A)
% 6.94/7.18        | (v2_struct_0 @ sk_A))),
% 6.94/7.18      inference('sup-', [status(thm)], ['199', '201'])).
% 6.94/7.18  thf('203', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('204', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('206', plain, ((v2_pre_topc @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('207', plain,
% 6.94/7.18      (((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['202', '203', '204', '205', '206'])).
% 6.94/7.18  thf('208', plain, (~ (v2_struct_0 @ sk_A)),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('209', plain, ((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['207', '208'])).
% 6.94/7.18  thf('210', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         ((v3_pre_topc @ 
% 6.94/7.18           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 6.94/7.18           X0)
% 6.94/7.18          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['198', '209'])).
% 6.94/7.18  thf('211', plain,
% 6.94/7.18      (((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 6.94/7.18         | (v3_pre_topc @ 
% 6.94/7.18            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 6.94/7.18            sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['191', '210'])).
% 6.94/7.18  thf('212', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('213', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('split', [status(esa)], ['140'])).
% 6.94/7.18  thf(redefinition_k8_relset_1, axiom,
% 6.94/7.18    (![A:$i,B:$i,C:$i,D:$i]:
% 6.94/7.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.94/7.18       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 6.94/7.18  thf('214', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 6.94/7.18          | ((k8_relset_1 @ X1 @ X2 @ X0 @ X3) = (k10_relat_1 @ X0 @ X3)))),
% 6.94/7.18      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 6.94/7.18  thf('215', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 6.94/7.18            (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['213', '214'])).
% 6.94/7.18  thf('216', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18             (k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 6.94/7.18             (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18             = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0))
% 6.94/7.18           | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['212', '215'])).
% 6.94/7.18  thf('217', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('sup-', [status(thm)], ['67', '68'])).
% 6.94/7.18  thf('218', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 6.94/7.18            (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['216', '217'])).
% 6.94/7.18  thf('219', plain,
% 6.94/7.18      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['66', '69'])).
% 6.94/7.18  thf('220', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('221', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('222', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 6.94/7.18  thf('223', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 6.94/7.18      inference('sat_resolution*', [status(thm)], ['163'])).
% 6.94/7.18  thf('224', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 6.94/7.18           = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['222', '223'])).
% 6.94/7.18  thf('225', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('226', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('227', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('228', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 6.94/7.18            (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['213', '214'])).
% 6.94/7.18  thf('229', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['227', '228'])).
% 6.94/7.18  thf('230', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18             (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18             = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0))
% 6.94/7.18           | ~ (l1_struct_0 @ sk_A)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['226', '229'])).
% 6.94/7.18  thf('231', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('232', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['230', '231'])).
% 6.94/7.18  thf('233', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('234', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('235', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['232', '233', '234'])).
% 6.94/7.18  thf('236', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 6.94/7.18      inference('sat_resolution*', [status(thm)], ['163'])).
% 6.94/7.18  thf('237', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 6.94/7.18           = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['235', '236'])).
% 6.94/7.18  thf('238', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))
% 6.94/7.18          | ~ (l1_struct_0 @ sk_A))),
% 6.94/7.18      inference('sup+', [status(thm)], ['225', '237'])).
% 6.94/7.18  thf('239', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('240', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)
% 6.94/7.18           = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['238', '239'])).
% 6.94/7.18  thf('241', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('242', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('243', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('244', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('split', [status(esa)], ['140'])).
% 6.94/7.18  thf('245', plain,
% 6.94/7.18      ((((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18          (k1_zfmisc_1 @ 
% 6.94/7.18           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ 
% 6.94/7.18            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 6.94/7.18         | ~ (l1_struct_0 @ sk_A)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['243', '244'])).
% 6.94/7.18  thf('246', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('247', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['245', '246'])).
% 6.94/7.18  thf('248', plain,
% 6.94/7.18      ((((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18          (k1_zfmisc_1 @ 
% 6.94/7.18           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ 
% 6.94/7.18            (k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 6.94/7.18         | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['242', '247'])).
% 6.94/7.18  thf('249', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('250', plain,
% 6.94/7.18      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['66', '69'])).
% 6.94/7.18  thf('251', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('sup-', [status(thm)], ['67', '68'])).
% 6.94/7.18  thf('252', plain,
% 6.94/7.18      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['248', '249', '250', '251'])).
% 6.94/7.18  thf('253', plain,
% 6.94/7.18      ((((m1_subset_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 6.94/7.18          (k1_zfmisc_1 @ 
% 6.94/7.18           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18         | ~ (l1_struct_0 @ sk_A)))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['241', '252'])).
% 6.94/7.18  thf('254', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('255', plain,
% 6.94/7.18      (((m1_subset_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 6.94/7.18         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 6.94/7.18      inference('demod', [status(thm)], ['253', '254'])).
% 6.94/7.18  thf('256', plain,
% 6.94/7.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18         (k1_zfmisc_1 @ 
% 6.94/7.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 6.94/7.18      inference('sat_resolution*', [status(thm)], ['163'])).
% 6.94/7.18  thf('257', plain,
% 6.94/7.18      ((m1_subset_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 6.94/7.18        (k1_zfmisc_1 @ 
% 6.94/7.18         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['255', '256'])).
% 6.94/7.18  thf('258', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 6.94/7.18          | ((k8_relset_1 @ X1 @ X2 @ X0 @ X3) = (k10_relat_1 @ X0 @ X3)))),
% 6.94/7.18      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 6.94/7.18  thf('259', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)
% 6.94/7.18           = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0))),
% 6.94/7.18      inference('sup-', [status(thm)], ['257', '258'])).
% 6.94/7.18  thf('260', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         ((k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 6.94/7.18           = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0))),
% 6.94/7.18      inference('sup+', [status(thm)], ['240', '259'])).
% 6.94/7.18  thf('261', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 6.94/7.18           = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['224', '260'])).
% 6.94/7.18  thf('262', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('263', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('264', plain,
% 6.94/7.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.18  thf('265', plain,
% 6.94/7.18      (![X4 : $i, X5 : $i]:
% 6.94/7.18         (((k8_relset_1 @ X5 @ X5 @ (k6_partfun1 @ X5) @ X4) = (X4))
% 6.94/7.18          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 6.94/7.18      inference('cnf', [status(esa)], [t171_funct_2])).
% 6.94/7.18  thf('266', plain,
% 6.94/7.18      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 6.94/7.18      inference('sup-', [status(thm)], ['264', '265'])).
% 6.94/7.18  thf('267', plain,
% 6.94/7.18      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))
% 6.94/7.18        | ~ (l1_struct_0 @ sk_A))),
% 6.94/7.18      inference('sup+', [status(thm)], ['263', '266'])).
% 6.94/7.18  thf('268', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('269', plain,
% 6.94/7.18      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 6.94/7.18      inference('demod', [status(thm)], ['267', '268'])).
% 6.94/7.18  thf('270', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 6.94/7.18           = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['235', '236'])).
% 6.94/7.18  thf('271', plain,
% 6.94/7.18      (((k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 6.94/7.18      inference('demod', [status(thm)], ['269', '270'])).
% 6.94/7.18  thf('272', plain,
% 6.94/7.18      ((((k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ sk_B) = (sk_B))
% 6.94/7.18        | ~ (l1_struct_0 @ sk_A))),
% 6.94/7.18      inference('sup+', [status(thm)], ['262', '271'])).
% 6.94/7.18  thf('273', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('274', plain,
% 6.94/7.18      (((k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 6.94/7.18      inference('demod', [status(thm)], ['272', '273'])).
% 6.94/7.18  thf('275', plain,
% 6.94/7.18      (((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v3_pre_topc @ sk_B @ sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['211', '261', '274'])).
% 6.94/7.18  thf('276', plain,
% 6.94/7.18      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['155', '164'])).
% 6.94/7.18  thf('277', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('278', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('279', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (~ (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['171', '277', '278'])).
% 6.94/7.18  thf('280', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('281', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('282', plain,
% 6.94/7.18      (((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['280', '281'])).
% 6.94/7.18  thf('283', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('284', plain,
% 6.94/7.18      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['282', '283'])).
% 6.94/7.18  thf('285', plain,
% 6.94/7.18      (![X14 : $i, X15 : $i]:
% 6.94/7.18         ((zip_tseitin_0 @ X14 @ X15) | ((k2_struct_0 @ X15) != (k1_xboole_0)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.94/7.18  thf('286', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ sk_A)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['284', '285'])).
% 6.94/7.18  thf('287', plain,
% 6.94/7.18      ((![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('simplify', [status(thm)], ['286'])).
% 6.94/7.18  thf('288', plain,
% 6.94/7.18      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 6.94/7.18        | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['184', '185'])).
% 6.94/7.18  thf('289', plain,
% 6.94/7.18      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['287', '288'])).
% 6.94/7.18  thf('290', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('291', plain,
% 6.94/7.18      (((zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['289', '290'])).
% 6.94/7.18  thf('292', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          (zip_tseitin_1 @ X0 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['279', '291'])).
% 6.94/7.18  thf('293', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         ((v3_pre_topc @ 
% 6.94/7.18           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 6.94/7.18           X0)
% 6.94/7.18          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['198', '209'])).
% 6.94/7.18  thf('294', plain,
% 6.94/7.18      (((v3_pre_topc @ 
% 6.94/7.18         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18          (k6_partfun1 @ k1_xboole_0) @ sk_B) @ 
% 6.94/7.18         sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['292', '293'])).
% 6.94/7.18  thf('295', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('296', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('297', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('298', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 6.94/7.18           = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['224', '260'])).
% 6.94/7.18  thf('299', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 6.94/7.18            (k6_partfun1 @ k1_xboole_0) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['297', '298'])).
% 6.94/7.18  thf('300', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('301', plain,
% 6.94/7.18      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('clc', [status(thm)], ['275', '276'])).
% 6.94/7.18  thf('302', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 6.94/7.18            (k6_partfun1 @ k1_xboole_0) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['299', '300', '301'])).
% 6.94/7.18  thf('303', plain,
% 6.94/7.18      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['282', '283'])).
% 6.94/7.18  thf('304', plain,
% 6.94/7.18      ((![X0 : $i]:
% 6.94/7.18          ((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 6.94/7.18            (k6_partfun1 @ k1_xboole_0) @ X0)
% 6.94/7.18            = (k10_relat_1 @ (k6_partfun1 @ k1_xboole_0) @ X0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['302', '303'])).
% 6.94/7.18  thf('305', plain,
% 6.94/7.18      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['282', '283'])).
% 6.94/7.18  thf('306', plain,
% 6.94/7.18      (((k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 6.94/7.18      inference('demod', [status(thm)], ['272', '273'])).
% 6.94/7.18  thf('307', plain,
% 6.94/7.18      ((((k10_relat_1 @ (k6_partfun1 @ k1_xboole_0) @ sk_B) = (sk_B)))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('sup+', [status(thm)], ['305', '306'])).
% 6.94/7.18  thf('308', plain,
% 6.94/7.18      (((v3_pre_topc @ sk_B @ sk_A))
% 6.94/7.18         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['294', '295', '296', '304', '307'])).
% 6.94/7.18  thf('309', plain,
% 6.94/7.18      (~
% 6.94/7.18       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('demod', [status(thm)], ['165', '308'])).
% 6.94/7.18  thf('310', plain,
% 6.94/7.18      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 6.94/7.18       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('split', [status(esa)], ['135'])).
% 6.94/7.18  thf('311', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 6.94/7.18      inference('sat_resolution*', [status(thm)], ['309', '310'])).
% 6.94/7.18  thf('312', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (~ (v1_funct_1 @ X0)
% 6.94/7.18          | ~ (v5_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18          | ~ (m1_subset_1 @ X0 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['133', '311'])).
% 6.94/7.18  thf('313', plain,
% 6.94/7.18      ((~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 6.94/7.18      inference('sup-', [status(thm)], ['96', '312'])).
% 6.94/7.18  thf('314', plain,
% 6.94/7.18      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['80', '81'])).
% 6.94/7.18  thf('315', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('demod', [status(thm)], ['90', '91'])).
% 6.94/7.18  thf('316', plain,
% 6.94/7.18      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('demod', [status(thm)], ['313', '314', '315'])).
% 6.94/7.18  thf('317', plain,
% 6.94/7.18      ((~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         <= (~
% 6.94/7.18             ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('split', [status(esa)], ['159'])).
% 6.94/7.18  thf('318', plain,
% 6.94/7.18      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('clc', [status(thm)], ['35', '36'])).
% 6.94/7.18  thf('319', plain,
% 6.94/7.18      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18         <= (~
% 6.94/7.18             ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))))),
% 6.94/7.18      inference('demod', [status(thm)], ['317', '318'])).
% 6.94/7.18  thf('320', plain,
% 6.94/7.18      (~
% 6.94/7.18       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 6.94/7.18         (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('sat_resolution*', [status(thm)], ['309'])).
% 6.94/7.18  thf('321', plain,
% 6.94/7.18      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 6.94/7.18          (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('simpl_trail', [status(thm)], ['319', '320'])).
% 6.94/7.18  thf('322', plain,
% 6.94/7.18      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['316', '321'])).
% 6.94/7.18  thf('323', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('324', plain,
% 6.94/7.18      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v5_pre_topc @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('demod', [status(thm)], ['26', '323'])).
% 6.94/7.18  thf('325', plain,
% 6.94/7.18      (![X6 : $i]:
% 6.94/7.18         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 6.94/7.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.94/7.18  thf('326', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('327', plain,
% 6.94/7.18      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 6.94/7.18      inference('sup+', [status(thm)], ['325', '326'])).
% 6.94/7.18  thf('328', plain, ((l1_struct_0 @ sk_A)),
% 6.94/7.18      inference('sup-', [status(thm)], ['23', '24'])).
% 6.94/7.18  thf('329', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('demod', [status(thm)], ['327', '328'])).
% 6.94/7.18  thf('330', plain,
% 6.94/7.18      ((~ (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18        | (v5_pre_topc @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('demod', [status(thm)], ['324', '329'])).
% 6.94/7.18  thf('331', plain,
% 6.94/7.18      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['316', '321'])).
% 6.94/7.18  thf('332', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('333', plain,
% 6.94/7.18      (~ (v5_pre_topc @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('demod', [status(thm)], ['331', '332'])).
% 6.94/7.18  thf('334', plain,
% 6.94/7.18      (~ (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['330', '333'])).
% 6.94/7.18  thf('335', plain,
% 6.94/7.18      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (k1_zfmisc_1 @ 
% 6.94/7.18         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 6.94/7.18      inference('clc', [status(thm)], ['41', '42'])).
% 6.94/7.18  thf('336', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('337', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('338', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('339', plain,
% 6.94/7.18      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 6.94/7.18      inference('demod', [status(thm)], ['335', '336', '337', '338'])).
% 6.94/7.18  thf('340', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('341', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('342', plain,
% 6.94/7.18      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.94/7.18         (~ (l1_pre_topc @ X25)
% 6.94/7.18          | ~ (zip_tseitin_0 @ X25 @ X26)
% 6.94/7.18          | (zip_tseitin_2 @ X27 @ X25 @ X26)
% 6.94/7.18          | ~ (m1_subset_1 @ X27 @ 
% 6.94/7.18               (k1_zfmisc_1 @ 
% 6.94/7.18                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 6.94/7.18          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 6.94/7.18          | ~ (v1_funct_1 @ X27)
% 6.94/7.18          | ~ (l1_pre_topc @ X26))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_7])).
% 6.94/7.18  thf('343', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X1 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (l1_pre_topc @ X0)
% 6.94/7.18          | ~ (v1_funct_1 @ X1)
% 6.94/7.18          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ 
% 6.94/7.18               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 6.94/7.18          | (zip_tseitin_2 @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['341', '342'])).
% 6.94/7.18  thf('344', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('345', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['54', '55'])).
% 6.94/7.18  thf('346', plain,
% 6.94/7.18      (![X0 : $i, X1 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X1 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (l1_pre_topc @ X0)
% 6.94/7.18          | ~ (v1_funct_1 @ X1)
% 6.94/7.18          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.94/7.18          | (zip_tseitin_2 @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0)
% 6.94/7.18          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['343', '344', '345'])).
% 6.94/7.18  thf('347', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 6.94/7.18               (u1_struct_0 @ sk_A))
% 6.94/7.18          | ~ (v1_funct_1 @ X0)
% 6.94/7.18          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['340', '346'])).
% 6.94/7.18  thf('348', plain,
% 6.94/7.18      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['6', '7'])).
% 6.94/7.18  thf('349', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('clc', [status(thm)], ['54', '55'])).
% 6.94/7.18  thf('350', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ 
% 6.94/7.18             (k1_zfmisc_1 @ 
% 6.94/7.18              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 6.94/7.18          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18               (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.94/7.18          | ~ (v1_funct_1 @ X0))),
% 6.94/7.18      inference('demod', [status(thm)], ['347', '348', '349'])).
% 6.94/7.18  thf('351', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('352', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('353', plain,
% 6.94/7.18      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('demod', [status(thm)], ['66', '69'])).
% 6.94/7.18  thf('354', plain,
% 6.94/7.18      (![X14 : $i, X15 : $i]:
% 6.94/7.18         ((zip_tseitin_0 @ X14 @ X15) | ((k2_struct_0 @ X15) != (k1_xboole_0)))),
% 6.94/7.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.94/7.18  thf('355', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (((u1_struct_0 @ sk_A) != (k1_xboole_0))
% 6.94/7.18          | (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['353', '354'])).
% 6.94/7.18  thf('356', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('357', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (((k1_xboole_0) != (k1_xboole_0))
% 6.94/7.18          | (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('demod', [status(thm)], ['355', '356'])).
% 6.94/7.18  thf('358', plain,
% 6.94/7.18      (![X0 : $i]: (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('simplify', [status(thm)], ['357'])).
% 6.94/7.18  thf('359', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('360', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('361', plain,
% 6.94/7.18      (![X0 : $i]:
% 6.94/7.18         (~ (m1_subset_1 @ X0 @ 
% 6.94/7.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 6.94/7.18          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 6.94/7.18             (k6_tmap_1 @ sk_A @ sk_B))
% 6.94/7.18          | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 6.94/7.18          | ~ (v1_funct_1 @ X0))),
% 6.94/7.18      inference('demod', [status(thm)],
% 6.94/7.18                ['350', '351', '352', '358', '359', '360'])).
% 6.94/7.18  thf('362', plain,
% 6.94/7.18      ((~ (v1_funct_1 @ (k6_partfun1 @ k1_xboole_0))
% 6.94/7.18        | ~ (v1_funct_2 @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0 @ 
% 6.94/7.18             k1_xboole_0)
% 6.94/7.18        | (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 6.94/7.18      inference('sup-', [status(thm)], ['339', '361'])).
% 6.94/7.18  thf('363', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 6.94/7.18      inference('demod', [status(thm)], ['90', '91'])).
% 6.94/7.18  thf('364', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('365', plain, ((v1_funct_1 @ (k6_partfun1 @ k1_xboole_0))),
% 6.94/7.18      inference('demod', [status(thm)], ['363', '364'])).
% 6.94/7.18  thf('366', plain,
% 6.94/7.18      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 6.94/7.18        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.94/7.18      inference('clc', [status(thm)], ['80', '81'])).
% 6.94/7.18  thf('367', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('368', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('369', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.94/7.18      inference('clc', [status(thm)], ['95', '322'])).
% 6.94/7.18  thf('370', plain,
% 6.94/7.18      ((v1_funct_2 @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0 @ k1_xboole_0)),
% 6.94/7.18      inference('demod', [status(thm)], ['366', '367', '368', '369'])).
% 6.94/7.18  thf('371', plain,
% 6.94/7.18      ((zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 6.94/7.18        (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 6.94/7.18      inference('demod', [status(thm)], ['362', '365', '370'])).
% 6.94/7.18  thf('372', plain, ($false), inference('demod', [status(thm)], ['334', '371'])).
% 6.94/7.18  
% 6.94/7.18  % SZS output end Refutation
% 6.94/7.18  
% 6.94/7.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
