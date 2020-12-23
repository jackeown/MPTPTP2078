%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z5Gg4BVijL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:44 EST 2020

% Result     : Theorem 6.18s
% Output     : Refutation 6.18s
% Verified   : 
% Statistics : Number of formulae       :  263 (3661 expanded)
%              Number of leaves         :   65 (1153 expanded)
%              Depth                    :   18
%              Number of atoms          : 1846 (51695 expanded)
%              Number of equality atoms :   97 ( 920 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t68_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( v5_pre_topc @ C @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( v5_pre_topc @ C @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_tex_2])).

thf('0',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [B: $i,A: $i] :
      ( ( ( ( k2_struct_0 @ B )
          = k1_xboole_0 )
       => ( ( k2_struct_0 @ A )
          = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_0 @ X53 @ X54 )
      | ( ( k2_struct_0 @ X53 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X50: $i] :
      ( ( l1_struct_0 @ X50 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v5_pre_topc @ C @ A @ B )
      <=> ! [D: $i] :
            ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) )).

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

thf('30',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( l1_pre_topc @ X64 )
      | ~ ( zip_tseitin_0 @ X64 @ X65 )
      | ( zip_tseitin_2 @ X66 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X65 ) @ ( u1_struct_0 @ X64 ) ) ) )
      | ~ ( v1_funct_2 @ X66 @ ( u1_struct_0 @ X65 ) @ ( u1_struct_0 @ X64 ) )
      | ~ ( v1_funct_1 @ X66 )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X36 @ X37 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X72: $i,X73: $i] :
      ( ~ ( v1_tdlat_3 @ X72 )
      | ( v3_pre_topc @ X73 @ X72 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) )
      | ~ ( l1_pre_topc @ X72 )
      | ~ ( v2_pre_topc @ X72 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X55: $i,X56: $i,X58: $i,X59: $i] :
      ( ( zip_tseitin_1 @ X55 @ X58 @ X56 @ X59 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X59 ) @ ( u1_struct_0 @ X56 ) @ X58 @ X55 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X60 @ X61 @ X62 ) @ X62 @ X61 @ X60 )
      | ( v5_pre_topc @ X62 @ X60 @ X61 )
      | ~ ( zip_tseitin_2 @ X62 @ X61 @ X60 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,
    ( ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','52'])).

thf('54',plain,(
    ~ ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['0','53'])).

thf('55',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_0 @ X53 @ X54 )
      | ( ( k2_struct_0 @ X53 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ sk_B_2 ) @ X0 )
      | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_2,axiom,(
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
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( r1_tarski @ ( k2_pre_topc @ A @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( v2_pre_topc @ X67 )
      | ~ ( l1_pre_topc @ X67 )
      | ( m1_subset_1 @ ( sk_D_1 @ X68 @ X67 @ X69 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( v5_pre_topc @ X68 @ X69 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X69 ) @ ( u1_struct_0 @ X67 ) ) ) )
      | ~ ( v1_funct_2 @ X68 @ ( u1_struct_0 @ X69 ) @ ( u1_struct_0 @ X67 ) )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( l1_pre_topc @ X69 )
      | ~ ( v2_pre_topc @ X69 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('63',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68','69'])).

thf('71',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['60','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('77',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_2 ) @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ( ( k2_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','79'])).

thf('81',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','52'])).

thf('82',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','52'])).

thf('83',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A )
    | ( ( k2_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_0 @ X53 @ X54 )
      | ( ( k2_struct_0 @ X53 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('86',plain,
    ( ( ( k2_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','52'])).

thf('88',plain,
    ( ( ( k2_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('90',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','52'])).

thf('91',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_struct_0 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A )
    | ( k1_xboole_0
      = ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','92'])).

thf('94',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('95',plain,
    ( k1_xboole_0
    = ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( v2_pre_topc @ X67 )
      | ~ ( l1_pre_topc @ X67 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X69 @ ( k8_relset_1 @ ( u1_struct_0 @ X69 ) @ ( u1_struct_0 @ X67 ) @ X68 @ ( sk_D_1 @ X68 @ X67 @ X69 ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X69 ) @ ( u1_struct_0 @ X67 ) @ X68 @ ( k2_pre_topc @ X67 @ ( sk_D_1 @ X68 @ X67 @ X69 ) ) ) )
      | ( v5_pre_topc @ X68 @ X69 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X69 ) @ ( u1_struct_0 @ X67 ) ) ) )
      | ~ ( v1_funct_2 @ X68 @ ( u1_struct_0 @ X69 ) @ ( u1_struct_0 @ X67 ) )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( l1_pre_topc @ X69 )
      | ~ ( v2_pre_topc @ X69 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('97',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ k1_xboole_0 @ ( k2_pre_topc @ sk_B_2 @ k1_xboole_0 ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ sk_B_2 ) @ X0 )
      | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('99',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('101',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_2 ) @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_2 ) @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( ( u1_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('105',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_2 ) @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','105'])).

thf('107',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('108',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_B_2 ) )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('110',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('112',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( u1_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['110','113'])).

thf('115',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','52'])).

thf('116',plain,
    ( ( ( u1_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('118',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( k1_xboole_0
    = ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('120',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('121',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k8_relset_1 @ X42 @ X43 @ X44 @ X43 )
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('124',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X40 @ X41 @ X39 )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('127',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('128',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('130',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('132',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X47: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X47 ) @ X47 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('134',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['132','133'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('135',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_partfun1 @ X46 @ X45 )
      | ( ( k1_relat_1 @ X46 )
        = X45 )
      | ~ ( v4_relat_1 @ X46 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('138',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('139',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('141',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('142',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['136','139','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('148',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('150',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( v1_tdlat_3 @ X74 )
      | ( v4_pre_topc @ X75 @ X74 )
      | ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X74 ) ) )
      | ~ ( l1_pre_topc @ X74 )
      | ~ ( v2_pre_topc @ X74 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','151'])).

thf('153',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('157',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v4_pre_topc @ X51 @ X52 )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = X51 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('164',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v2_pre_topc @ X52 )
      | ( ( k2_pre_topc @ X52 @ X51 )
       != X51 )
      | ( v4_pre_topc @ X51 @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('168',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('173',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('176',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['116','117'])).

thf('178',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('179',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','52'])).

thf('183',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['116','117'])).

thf('185',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','52'])).

thf('187',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['116','117'])).

thf('189',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['116','117'])).

thf('191',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('192',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('193',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['97','118','119','145','176','177','178','179','180','183','184','189','190','191','192','193','194'])).

thf('196',plain,(
    $false ),
    inference(demod,[status(thm)],['54','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z5Gg4BVijL
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:48:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 6.18/6.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.18/6.38  % Solved by: fo/fo7.sh
% 6.18/6.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.18/6.38  % done 7893 iterations in 5.930s
% 6.18/6.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.18/6.38  % SZS output start Refutation
% 6.18/6.38  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 6.18/6.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.18/6.38  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.18/6.38  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 6.18/6.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.18/6.38  thf(sk_A_type, type, sk_A: $i).
% 6.18/6.38  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 6.18/6.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.18/6.38  thf(sk_B_2_type, type, sk_B_2: $i).
% 6.18/6.38  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.18/6.38  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.18/6.38  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.18/6.38  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.18/6.38  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 6.18/6.38  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 6.18/6.38  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.18/6.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.18/6.38  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 6.18/6.38  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 6.18/6.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.18/6.38  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.18/6.38  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.18/6.38  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.18/6.38  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.18/6.38  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 6.18/6.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.18/6.38  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.18/6.38  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 6.18/6.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.18/6.38  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 6.18/6.38  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.18/6.38  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 6.18/6.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.18/6.38  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.18/6.38  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 6.18/6.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.18/6.38  thf(t68_tex_2, conjecture,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.18/6.38       ( ![B:$i]:
% 6.18/6.38         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 6.18/6.38           ( ![C:$i]:
% 6.18/6.38             ( ( ( v1_funct_1 @ C ) & 
% 6.18/6.38                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.18/6.38                 ( m1_subset_1 @
% 6.18/6.38                   C @ 
% 6.18/6.38                   ( k1_zfmisc_1 @
% 6.18/6.38                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.18/6.38               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 6.18/6.38  thf(zf_stmt_0, negated_conjecture,
% 6.18/6.38    (~( ![A:$i]:
% 6.18/6.38        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.18/6.38          ( ![B:$i]:
% 6.18/6.38            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 6.18/6.38              ( ![C:$i]:
% 6.18/6.38                ( ( ( v1_funct_1 @ C ) & 
% 6.18/6.38                    ( v1_funct_2 @
% 6.18/6.38                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.18/6.38                    ( m1_subset_1 @
% 6.18/6.38                      C @ 
% 6.18/6.38                      ( k1_zfmisc_1 @
% 6.18/6.38                        ( k2_zfmisc_1 @
% 6.18/6.38                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.18/6.38                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 6.18/6.38    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 6.18/6.38  thf('0', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf(t55_tops_2, axiom,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( l1_pre_topc @ A ) =>
% 6.18/6.38       ( ![B:$i]:
% 6.18/6.38         ( ( l1_pre_topc @ B ) =>
% 6.18/6.38           ( ![C:$i]:
% 6.18/6.38             ( ( ( m1_subset_1 @
% 6.18/6.38                   C @ 
% 6.18/6.38                   ( k1_zfmisc_1 @
% 6.18/6.38                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 6.18/6.38                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.18/6.38                 ( v1_funct_1 @ C ) ) =>
% 6.18/6.38               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 6.18/6.38                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 6.18/6.38                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 6.18/6.38                   ( ![D:$i]:
% 6.18/6.38                     ( ( m1_subset_1 @
% 6.18/6.38                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.18/6.38                       ( ( v3_pre_topc @ D @ B ) =>
% 6.18/6.38                         ( v3_pre_topc @
% 6.18/6.38                           ( k8_relset_1 @
% 6.18/6.38                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 6.18/6.38                           A ) ) ) ) ) ) ) ) ) ) ))).
% 6.18/6.38  thf(zf_stmt_1, axiom,
% 6.18/6.38    (![B:$i,A:$i]:
% 6.18/6.38     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 6.18/6.38         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 6.18/6.38       ( zip_tseitin_0 @ B @ A ) ))).
% 6.18/6.38  thf('1', plain,
% 6.18/6.38      (![X53 : $i, X54 : $i]:
% 6.18/6.38         ((zip_tseitin_0 @ X53 @ X54) | ((k2_struct_0 @ X53) = (k1_xboole_0)))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.18/6.38  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.18/6.38  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.38  thf('3', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 6.18/6.38      inference('sup+', [status(thm)], ['1', '2'])).
% 6.18/6.38  thf(d3_struct_0, axiom,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 6.18/6.38  thf('4', plain,
% 6.18/6.38      (![X49 : $i]:
% 6.18/6.38         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 6.18/6.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.18/6.38  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.38  thf(t8_boole, axiom,
% 6.18/6.38    (![A:$i,B:$i]:
% 6.18/6.38     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 6.18/6.38  thf('6', plain,
% 6.18/6.38      (![X4 : $i, X5 : $i]:
% 6.18/6.38         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 6.18/6.38      inference('cnf', [status(esa)], [t8_boole])).
% 6.18/6.38  thf('7', plain,
% 6.18/6.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['5', '6'])).
% 6.18/6.38  thf(t113_zfmisc_1, axiom,
% 6.18/6.38    (![A:$i,B:$i]:
% 6.18/6.38     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.18/6.38       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.18/6.38  thf('8', plain,
% 6.18/6.38      (![X12 : $i, X13 : $i]:
% 6.18/6.38         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 6.18/6.38          | ((X13) != (k1_xboole_0)))),
% 6.18/6.38      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.18/6.38  thf('9', plain,
% 6.18/6.38      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 6.18/6.38      inference('simplify', [status(thm)], ['8'])).
% 6.18/6.38  thf('10', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('sup+', [status(thm)], ['7', '9'])).
% 6.18/6.38  thf('11', plain,
% 6.18/6.38      ((m1_subset_1 @ sk_C_1 @ 
% 6.18/6.38        (k1_zfmisc_1 @ 
% 6.18/6.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf(t3_subset, axiom,
% 6.18/6.38    (![A:$i,B:$i]:
% 6.18/6.38     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.18/6.38  thf('12', plain,
% 6.18/6.38      (![X20 : $i, X21 : $i]:
% 6.18/6.38         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 6.18/6.38      inference('cnf', [status(esa)], [t3_subset])).
% 6.18/6.38  thf('13', plain,
% 6.18/6.38      ((r1_tarski @ sk_C_1 @ 
% 6.18/6.38        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['11', '12'])).
% 6.18/6.38  thf('14', plain,
% 6.18/6.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['5', '6'])).
% 6.18/6.38  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.18/6.38  thf('15', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 6.18/6.38      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.18/6.38  thf(d10_xboole_0, axiom,
% 6.18/6.38    (![A:$i,B:$i]:
% 6.18/6.38     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.18/6.38  thf('16', plain,
% 6.18/6.38      (![X0 : $i, X2 : $i]:
% 6.18/6.38         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.18/6.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.18/6.38  thf('17', plain,
% 6.18/6.38      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['15', '16'])).
% 6.18/6.38  thf('18', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         (~ (r1_tarski @ X1 @ X0)
% 6.18/6.38          | ~ (v1_xboole_0 @ X0)
% 6.18/6.38          | ((X1) = (k1_xboole_0)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['14', '17'])).
% 6.18/6.38  thf('19', plain,
% 6.18/6.38      ((((sk_C_1) = (k1_xboole_0))
% 6.18/6.38        | ~ (v1_xboole_0 @ 
% 6.18/6.38             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 6.18/6.38      inference('sup-', [status(thm)], ['13', '18'])).
% 6.18/6.38  thf('20', plain,
% 6.18/6.38      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.18/6.38        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 6.18/6.38        | ((sk_C_1) = (k1_xboole_0)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['10', '19'])).
% 6.18/6.38  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.38  thf('22', plain,
% 6.18/6.38      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)) | ((sk_C_1) = (k1_xboole_0)))),
% 6.18/6.38      inference('demod', [status(thm)], ['20', '21'])).
% 6.18/6.38  thf('23', plain,
% 6.18/6.38      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_2))
% 6.18/6.38        | ~ (l1_struct_0 @ sk_B_2)
% 6.18/6.38        | ((sk_C_1) = (k1_xboole_0)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['4', '22'])).
% 6.18/6.38  thf('24', plain, ((l1_pre_topc @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf(dt_l1_pre_topc, axiom,
% 6.18/6.38    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 6.18/6.38  thf('25', plain,
% 6.18/6.38      (![X50 : $i]: ((l1_struct_0 @ X50) | ~ (l1_pre_topc @ X50))),
% 6.18/6.38      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 6.18/6.38  thf('26', plain, ((l1_struct_0 @ sk_B_2)),
% 6.18/6.38      inference('sup-', [status(thm)], ['24', '25'])).
% 6.18/6.38  thf('27', plain,
% 6.18/6.38      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_2)) | ((sk_C_1) = (k1_xboole_0)))),
% 6.18/6.38      inference('demod', [status(thm)], ['23', '26'])).
% 6.18/6.38  thf('28', plain,
% 6.18/6.38      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | ((sk_C_1) = (k1_xboole_0)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['3', '27'])).
% 6.18/6.38  thf('29', plain,
% 6.18/6.38      ((m1_subset_1 @ sk_C_1 @ 
% 6.18/6.38        (k1_zfmisc_1 @ 
% 6.18/6.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 6.18/6.38  thf(zf_stmt_3, axiom,
% 6.18/6.38    (![C:$i,B:$i,A:$i]:
% 6.18/6.38     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 6.18/6.38       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 6.18/6.38         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 6.18/6.38  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 6.18/6.38  thf(zf_stmt_5, axiom,
% 6.18/6.38    (![D:$i,C:$i,B:$i,A:$i]:
% 6.18/6.38     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 6.18/6.38       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.18/6.38         ( ( v3_pre_topc @ D @ B ) =>
% 6.18/6.38           ( v3_pre_topc @
% 6.18/6.38             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 6.18/6.38             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 6.18/6.38  thf(zf_stmt_7, axiom,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( l1_pre_topc @ A ) =>
% 6.18/6.38       ( ![B:$i]:
% 6.18/6.38         ( ( l1_pre_topc @ B ) =>
% 6.18/6.38           ( ![C:$i]:
% 6.18/6.38             ( ( ( v1_funct_1 @ C ) & 
% 6.18/6.38                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.18/6.38                 ( m1_subset_1 @
% 6.18/6.38                   C @ 
% 6.18/6.38                   ( k1_zfmisc_1 @
% 6.18/6.38                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.18/6.38               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 6.18/6.38  thf('30', plain,
% 6.18/6.38      (![X64 : $i, X65 : $i, X66 : $i]:
% 6.18/6.38         (~ (l1_pre_topc @ X64)
% 6.18/6.38          | ~ (zip_tseitin_0 @ X64 @ X65)
% 6.18/6.38          | (zip_tseitin_2 @ X66 @ X64 @ X65)
% 6.18/6.38          | ~ (m1_subset_1 @ X66 @ 
% 6.18/6.38               (k1_zfmisc_1 @ 
% 6.18/6.38                (k2_zfmisc_1 @ (u1_struct_0 @ X65) @ (u1_struct_0 @ X64))))
% 6.18/6.38          | ~ (v1_funct_2 @ X66 @ (u1_struct_0 @ X65) @ (u1_struct_0 @ X64))
% 6.18/6.38          | ~ (v1_funct_1 @ X66)
% 6.18/6.38          | ~ (l1_pre_topc @ X65))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_7])).
% 6.18/6.38  thf('31', plain,
% 6.18/6.38      ((~ (l1_pre_topc @ sk_A)
% 6.18/6.38        | ~ (v1_funct_1 @ sk_C_1)
% 6.18/6.38        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 6.18/6.38             (u1_struct_0 @ sk_B_2))
% 6.18/6.38        | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ~ (l1_pre_topc @ sk_B_2))),
% 6.18/6.38      inference('sup-', [status(thm)], ['29', '30'])).
% 6.18/6.38  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('33', plain, ((v1_funct_1 @ sk_C_1)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('34', plain,
% 6.18/6.38      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('35', plain, ((l1_pre_topc @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('36', plain,
% 6.18/6.38      (((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 6.18/6.38  thf('37', plain,
% 6.18/6.38      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('sup-', [status(thm)], ['28', '36'])).
% 6.18/6.38  thf('38', plain,
% 6.18/6.38      ((m1_subset_1 @ sk_C_1 @ 
% 6.18/6.38        (k1_zfmisc_1 @ 
% 6.18/6.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf(dt_k8_relset_1, axiom,
% 6.18/6.38    (![A:$i,B:$i,C:$i,D:$i]:
% 6.18/6.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.18/6.38       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.18/6.38  thf('39', plain,
% 6.18/6.38      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 6.18/6.38         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 6.18/6.38          | (m1_subset_1 @ (k8_relset_1 @ X36 @ X37 @ X35 @ X38) @ 
% 6.18/6.38             (k1_zfmisc_1 @ X36)))),
% 6.18/6.38      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 6.18/6.38  thf('40', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         (m1_subset_1 @ 
% 6.18/6.38          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 6.18/6.38           sk_C_1 @ X0) @ 
% 6.18/6.38          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['38', '39'])).
% 6.18/6.38  thf(t17_tdlat_3, axiom,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.18/6.38       ( ( v1_tdlat_3 @ A ) <=>
% 6.18/6.38         ( ![B:$i]:
% 6.18/6.38           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.18/6.38             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 6.18/6.38  thf('41', plain,
% 6.18/6.38      (![X72 : $i, X73 : $i]:
% 6.18/6.38         (~ (v1_tdlat_3 @ X72)
% 6.18/6.38          | (v3_pre_topc @ X73 @ X72)
% 6.18/6.38          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 6.18/6.38          | ~ (l1_pre_topc @ X72)
% 6.18/6.38          | ~ (v2_pre_topc @ X72))),
% 6.18/6.38      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 6.18/6.38  thf('42', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         (~ (v2_pre_topc @ sk_A)
% 6.18/6.38          | ~ (l1_pre_topc @ sk_A)
% 6.18/6.38          | (v3_pre_topc @ 
% 6.18/6.38             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 6.18/6.38              sk_C_1 @ X0) @ 
% 6.18/6.38             sk_A)
% 6.18/6.38          | ~ (v1_tdlat_3 @ sk_A))),
% 6.18/6.38      inference('sup-', [status(thm)], ['40', '41'])).
% 6.18/6.38  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('45', plain, ((v1_tdlat_3 @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('46', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         (v3_pre_topc @ 
% 6.18/6.38          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 6.18/6.38           sk_C_1 @ X0) @ 
% 6.18/6.38          sk_A)),
% 6.18/6.38      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 6.18/6.38  thf('47', plain,
% 6.18/6.38      (![X55 : $i, X56 : $i, X58 : $i, X59 : $i]:
% 6.18/6.38         ((zip_tseitin_1 @ X55 @ X58 @ X56 @ X59)
% 6.18/6.38          | ~ (v3_pre_topc @ 
% 6.18/6.38               (k8_relset_1 @ (u1_struct_0 @ X59) @ (u1_struct_0 @ X56) @ 
% 6.18/6.38                X58 @ X55) @ 
% 6.18/6.38               X59))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.18/6.38  thf('48', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 6.18/6.38      inference('sup-', [status(thm)], ['46', '47'])).
% 6.18/6.38  thf('49', plain,
% 6.18/6.38      (![X60 : $i, X61 : $i, X62 : $i]:
% 6.18/6.38         (~ (zip_tseitin_1 @ (sk_D @ X60 @ X61 @ X62) @ X62 @ X61 @ X60)
% 6.18/6.38          | (v5_pre_topc @ X62 @ X60 @ X61)
% 6.18/6.38          | ~ (zip_tseitin_2 @ X62 @ X61 @ X60))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.18/6.38  thf('50', plain,
% 6.18/6.38      ((~ (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 6.18/6.38      inference('sup-', [status(thm)], ['48', '49'])).
% 6.18/6.38  thf('51', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('52', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 6.18/6.38      inference('clc', [status(thm)], ['50', '51'])).
% 6.18/6.38  thf('53', plain, (((sk_C_1) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['37', '52'])).
% 6.18/6.38  thf('54', plain, (~ (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 6.18/6.38      inference('demod', [status(thm)], ['0', '53'])).
% 6.18/6.38  thf('55', plain,
% 6.18/6.38      (![X53 : $i, X54 : $i]:
% 6.18/6.38         ((zip_tseitin_0 @ X53 @ X54) | ((k2_struct_0 @ X53) = (k1_xboole_0)))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.18/6.38  thf('56', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 6.18/6.38      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.18/6.38  thf('57', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.38         ((r1_tarski @ (k2_struct_0 @ X0) @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 6.18/6.38      inference('sup+', [status(thm)], ['55', '56'])).
% 6.18/6.38  thf('58', plain,
% 6.18/6.38      (((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 6.18/6.38  thf('59', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         ((r1_tarski @ (k2_struct_0 @ sk_B_2) @ X0)
% 6.18/6.38          | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('sup-', [status(thm)], ['57', '58'])).
% 6.18/6.38  thf('60', plain,
% 6.18/6.38      (![X49 : $i]:
% 6.18/6.38         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 6.18/6.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.18/6.38  thf('61', plain,
% 6.18/6.38      ((m1_subset_1 @ sk_C_1 @ 
% 6.18/6.38        (k1_zfmisc_1 @ 
% 6.18/6.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf(t56_tops_2, axiom,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.18/6.38       ( ![B:$i]:
% 6.18/6.38         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 6.18/6.38           ( ![C:$i]:
% 6.18/6.38             ( ( ( v1_funct_1 @ C ) & 
% 6.18/6.38                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.18/6.38                 ( m1_subset_1 @
% 6.18/6.38                   C @ 
% 6.18/6.38                   ( k1_zfmisc_1 @
% 6.18/6.38                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.18/6.38               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 6.18/6.38                 ( ![D:$i]:
% 6.18/6.38                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.18/6.38                     ( r1_tarski @
% 6.18/6.38                       ( k2_pre_topc @
% 6.18/6.38                         A @ 
% 6.18/6.38                         ( k8_relset_1 @
% 6.18/6.38                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 6.18/6.38                       ( k8_relset_1 @
% 6.18/6.38                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 6.18/6.38                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 6.18/6.38  thf('62', plain,
% 6.18/6.38      (![X67 : $i, X68 : $i, X69 : $i]:
% 6.18/6.38         (~ (v2_pre_topc @ X67)
% 6.18/6.38          | ~ (l1_pre_topc @ X67)
% 6.18/6.38          | (m1_subset_1 @ (sk_D_1 @ X68 @ X67 @ X69) @ 
% 6.18/6.38             (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 6.18/6.38          | (v5_pre_topc @ X68 @ X69 @ X67)
% 6.18/6.38          | ~ (m1_subset_1 @ X68 @ 
% 6.18/6.38               (k1_zfmisc_1 @ 
% 6.18/6.38                (k2_zfmisc_1 @ (u1_struct_0 @ X69) @ (u1_struct_0 @ X67))))
% 6.18/6.38          | ~ (v1_funct_2 @ X68 @ (u1_struct_0 @ X69) @ (u1_struct_0 @ X67))
% 6.18/6.38          | ~ (v1_funct_1 @ X68)
% 6.18/6.38          | ~ (l1_pre_topc @ X69)
% 6.18/6.38          | ~ (v2_pre_topc @ X69))),
% 6.18/6.38      inference('cnf', [status(esa)], [t56_tops_2])).
% 6.18/6.38  thf('63', plain,
% 6.18/6.38      ((~ (v2_pre_topc @ sk_A)
% 6.18/6.38        | ~ (l1_pre_topc @ sk_A)
% 6.18/6.38        | ~ (v1_funct_1 @ sk_C_1)
% 6.18/6.38        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 6.18/6.38             (u1_struct_0 @ sk_B_2))
% 6.18/6.38        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 6.18/6.38        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 6.18/6.38           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 6.18/6.38        | ~ (l1_pre_topc @ sk_B_2)
% 6.18/6.38        | ~ (v2_pre_topc @ sk_B_2))),
% 6.18/6.38      inference('sup-', [status(thm)], ['61', '62'])).
% 6.18/6.38  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('66', plain, ((v1_funct_1 @ sk_C_1)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('67', plain,
% 6.18/6.38      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('68', plain, ((l1_pre_topc @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('69', plain, ((v2_pre_topc @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('70', plain,
% 6.18/6.38      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 6.18/6.38        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 6.18/6.38           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 6.18/6.38      inference('demod', [status(thm)],
% 6.18/6.38                ['63', '64', '65', '66', '67', '68', '69'])).
% 6.18/6.38  thf('71', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('72', plain,
% 6.18/6.38      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 6.18/6.38        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))),
% 6.18/6.38      inference('clc', [status(thm)], ['70', '71'])).
% 6.18/6.38  thf('73', plain,
% 6.18/6.38      (![X20 : $i, X21 : $i]:
% 6.18/6.38         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 6.18/6.38      inference('cnf', [status(esa)], [t3_subset])).
% 6.18/6.38  thf('74', plain,
% 6.18/6.38      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('sup-', [status(thm)], ['72', '73'])).
% 6.18/6.38  thf('75', plain,
% 6.18/6.38      (((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ (k2_struct_0 @ sk_B_2))
% 6.18/6.38        | ~ (l1_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('sup+', [status(thm)], ['60', '74'])).
% 6.18/6.38  thf('76', plain, ((l1_struct_0 @ sk_B_2)),
% 6.18/6.38      inference('sup-', [status(thm)], ['24', '25'])).
% 6.18/6.38  thf('77', plain,
% 6.18/6.38      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ (k2_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('demod', [status(thm)], ['75', '76'])).
% 6.18/6.38  thf('78', plain,
% 6.18/6.38      (![X0 : $i, X2 : $i]:
% 6.18/6.38         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.18/6.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.18/6.38  thf('79', plain,
% 6.18/6.38      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_2) @ 
% 6.18/6.38           (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A))
% 6.18/6.38        | ((k2_struct_0 @ sk_B_2) = (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['77', '78'])).
% 6.18/6.38  thf('80', plain,
% 6.18/6.38      (((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ((k2_struct_0 @ sk_B_2) = (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['59', '79'])).
% 6.18/6.38  thf('81', plain, (((sk_C_1) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['37', '52'])).
% 6.18/6.38  thf('82', plain, (((sk_C_1) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['37', '52'])).
% 6.18/6.38  thf('83', plain,
% 6.18/6.38      (((zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ((k2_struct_0 @ sk_B_2) = (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A)))),
% 6.18/6.38      inference('demod', [status(thm)], ['80', '81', '82'])).
% 6.18/6.38  thf('84', plain,
% 6.18/6.38      (![X53 : $i, X54 : $i]:
% 6.18/6.38         ((zip_tseitin_0 @ X53 @ X54) | ((k2_struct_0 @ X53) = (k1_xboole_0)))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.18/6.38  thf('85', plain,
% 6.18/6.38      (((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 6.18/6.38  thf('86', plain,
% 6.18/6.38      ((((k2_struct_0 @ sk_B_2) = (k1_xboole_0))
% 6.18/6.38        | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('sup-', [status(thm)], ['84', '85'])).
% 6.18/6.38  thf('87', plain, (((sk_C_1) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['37', '52'])).
% 6.18/6.38  thf('88', plain,
% 6.18/6.38      ((((k2_struct_0 @ sk_B_2) = (k1_xboole_0))
% 6.18/6.38        | (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('demod', [status(thm)], ['86', '87'])).
% 6.18/6.38  thf('89', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 6.18/6.38      inference('clc', [status(thm)], ['50', '51'])).
% 6.18/6.38  thf('90', plain, (((sk_C_1) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['37', '52'])).
% 6.18/6.38  thf('91', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)),
% 6.18/6.38      inference('demod', [status(thm)], ['89', '90'])).
% 6.18/6.38  thf('92', plain, (((k2_struct_0 @ sk_B_2) = (k1_xboole_0))),
% 6.18/6.38      inference('clc', [status(thm)], ['88', '91'])).
% 6.18/6.38  thf('93', plain,
% 6.18/6.38      (((zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A)))),
% 6.18/6.38      inference('demod', [status(thm)], ['83', '92'])).
% 6.18/6.38  thf('94', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)),
% 6.18/6.38      inference('demod', [status(thm)], ['89', '90'])).
% 6.18/6.38  thf('95', plain, (((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('clc', [status(thm)], ['93', '94'])).
% 6.18/6.38  thf('96', plain,
% 6.18/6.38      (![X67 : $i, X68 : $i, X69 : $i]:
% 6.18/6.38         (~ (v2_pre_topc @ X67)
% 6.18/6.38          | ~ (l1_pre_topc @ X67)
% 6.18/6.38          | ~ (r1_tarski @ 
% 6.18/6.38               (k2_pre_topc @ X69 @ 
% 6.18/6.38                (k8_relset_1 @ (u1_struct_0 @ X69) @ (u1_struct_0 @ X67) @ 
% 6.18/6.38                 X68 @ (sk_D_1 @ X68 @ X67 @ X69))) @ 
% 6.18/6.38               (k8_relset_1 @ (u1_struct_0 @ X69) @ (u1_struct_0 @ X67) @ 
% 6.18/6.38                X68 @ (k2_pre_topc @ X67 @ (sk_D_1 @ X68 @ X67 @ X69))))
% 6.18/6.38          | (v5_pre_topc @ X68 @ X69 @ X67)
% 6.18/6.38          | ~ (m1_subset_1 @ X68 @ 
% 6.18/6.38               (k1_zfmisc_1 @ 
% 6.18/6.38                (k2_zfmisc_1 @ (u1_struct_0 @ X69) @ (u1_struct_0 @ X67))))
% 6.18/6.38          | ~ (v1_funct_2 @ X68 @ (u1_struct_0 @ X69) @ (u1_struct_0 @ X67))
% 6.18/6.38          | ~ (v1_funct_1 @ X68)
% 6.18/6.38          | ~ (l1_pre_topc @ X69)
% 6.18/6.38          | ~ (v2_pre_topc @ X69))),
% 6.18/6.38      inference('cnf', [status(esa)], [t56_tops_2])).
% 6.18/6.38  thf('97', plain,
% 6.18/6.38      ((~ (r1_tarski @ 
% 6.18/6.38           (k2_pre_topc @ sk_A @ 
% 6.18/6.38            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 6.18/6.38             k1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A))) @ 
% 6.18/6.38           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 6.18/6.38            k1_xboole_0 @ (k2_pre_topc @ sk_B_2 @ k1_xboole_0)))
% 6.18/6.38        | ~ (v2_pre_topc @ sk_A)
% 6.18/6.38        | ~ (l1_pre_topc @ sk_A)
% 6.18/6.38        | ~ (v1_funct_1 @ k1_xboole_0)
% 6.18/6.38        | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 6.18/6.38             (u1_struct_0 @ sk_B_2))
% 6.18/6.38        | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 6.18/6.38             (k1_zfmisc_1 @ 
% 6.18/6.38              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))
% 6.18/6.38        | (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2)
% 6.18/6.38        | ~ (l1_pre_topc @ sk_B_2)
% 6.18/6.38        | ~ (v2_pre_topc @ sk_B_2))),
% 6.18/6.38      inference('sup-', [status(thm)], ['95', '96'])).
% 6.18/6.38  thf('98', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         ((r1_tarski @ (k2_struct_0 @ sk_B_2) @ X0)
% 6.18/6.38          | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('sup-', [status(thm)], ['57', '58'])).
% 6.18/6.38  thf('99', plain,
% 6.18/6.38      (![X49 : $i]:
% 6.18/6.38         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 6.18/6.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.18/6.38  thf('100', plain,
% 6.18/6.38      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('sup-', [status(thm)], ['72', '73'])).
% 6.18/6.38  thf('101', plain,
% 6.18/6.38      (![X0 : $i, X2 : $i]:
% 6.18/6.38         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.18/6.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.18/6.38  thf('102', plain,
% 6.18/6.38      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_2) @ 
% 6.18/6.38           (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A))
% 6.18/6.38        | ((u1_struct_0 @ sk_B_2) = (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['100', '101'])).
% 6.18/6.38  thf('103', plain,
% 6.18/6.38      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_2) @ 
% 6.18/6.38           (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A))
% 6.18/6.38        | ~ (l1_struct_0 @ sk_B_2)
% 6.18/6.38        | ((u1_struct_0 @ sk_B_2) = (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['99', '102'])).
% 6.18/6.38  thf('104', plain, ((l1_struct_0 @ sk_B_2)),
% 6.18/6.38      inference('sup-', [status(thm)], ['24', '25'])).
% 6.18/6.38  thf('105', plain,
% 6.18/6.38      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_2) @ 
% 6.18/6.38           (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A))
% 6.18/6.38        | ((u1_struct_0 @ sk_B_2) = (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A)))),
% 6.18/6.38      inference('demod', [status(thm)], ['103', '104'])).
% 6.18/6.38  thf('106', plain,
% 6.18/6.38      (((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ((u1_struct_0 @ sk_B_2) = (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['98', '105'])).
% 6.18/6.38  thf('107', plain,
% 6.18/6.38      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ (k2_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('demod', [status(thm)], ['75', '76'])).
% 6.18/6.38  thf('108', plain,
% 6.18/6.38      (((r1_tarski @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_B_2))
% 6.18/6.38        | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('sup+', [status(thm)], ['106', '107'])).
% 6.18/6.38  thf('109', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         (~ (r1_tarski @ X1 @ X0)
% 6.18/6.38          | ~ (v1_xboole_0 @ X0)
% 6.18/6.38          | ((X1) = (k1_xboole_0)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['14', '17'])).
% 6.18/6.38  thf('110', plain,
% 6.18/6.38      (((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ((u1_struct_0 @ sk_B_2) = (k1_xboole_0))
% 6.18/6.38        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_2)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['108', '109'])).
% 6.18/6.38  thf('111', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 6.18/6.38      inference('sup+', [status(thm)], ['1', '2'])).
% 6.18/6.38  thf('112', plain,
% 6.18/6.38      (((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A)
% 6.18/6.38        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 6.18/6.38  thf('113', plain,
% 6.18/6.38      (((v1_xboole_0 @ (k2_struct_0 @ sk_B_2))
% 6.18/6.38        | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('sup-', [status(thm)], ['111', '112'])).
% 6.18/6.38  thf('114', plain,
% 6.18/6.38      ((((u1_struct_0 @ sk_B_2) = (k1_xboole_0))
% 6.18/6.38        | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('clc', [status(thm)], ['110', '113'])).
% 6.18/6.38  thf('115', plain, (((sk_C_1) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['37', '52'])).
% 6.18/6.38  thf('116', plain,
% 6.18/6.38      ((((u1_struct_0 @ sk_B_2) = (k1_xboole_0))
% 6.18/6.38        | (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('demod', [status(thm)], ['114', '115'])).
% 6.18/6.38  thf('117', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)),
% 6.18/6.38      inference('demod', [status(thm)], ['89', '90'])).
% 6.18/6.38  thf('118', plain, (((u1_struct_0 @ sk_B_2) = (k1_xboole_0))),
% 6.18/6.38      inference('clc', [status(thm)], ['116', '117'])).
% 6.18/6.38  thf('119', plain, (((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A))),
% 6.18/6.38      inference('clc', [status(thm)], ['93', '94'])).
% 6.18/6.38  thf(t4_subset_1, axiom,
% 6.18/6.38    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.18/6.38  thf('120', plain,
% 6.18/6.38      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 6.18/6.38      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.38  thf(t38_relset_1, axiom,
% 6.18/6.38    (![A:$i,B:$i,C:$i]:
% 6.18/6.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.18/6.38       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 6.18/6.38         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.18/6.38  thf('121', plain,
% 6.18/6.38      (![X42 : $i, X43 : $i, X44 : $i]:
% 6.18/6.38         (((k8_relset_1 @ X42 @ X43 @ X44 @ X43)
% 6.18/6.38            = (k1_relset_1 @ X42 @ X43 @ X44))
% 6.18/6.38          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 6.18/6.38      inference('cnf', [status(esa)], [t38_relset_1])).
% 6.18/6.38  thf('122', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 6.18/6.38           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['120', '121'])).
% 6.18/6.38  thf('123', plain,
% 6.18/6.38      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 6.18/6.38      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.38  thf(redefinition_k1_relset_1, axiom,
% 6.18/6.38    (![A:$i,B:$i,C:$i]:
% 6.18/6.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.18/6.38       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.18/6.38  thf('124', plain,
% 6.18/6.38      (![X39 : $i, X40 : $i, X41 : $i]:
% 6.18/6.38         (((k1_relset_1 @ X40 @ X41 @ X39) = (k1_relat_1 @ X39))
% 6.18/6.38          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 6.18/6.38      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.18/6.38  thf('125', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['123', '124'])).
% 6.18/6.38  thf('126', plain,
% 6.18/6.38      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 6.18/6.38      inference('simplify', [status(thm)], ['8'])).
% 6.18/6.38  thf(dt_k6_partfun1, axiom,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( m1_subset_1 @
% 6.18/6.38         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 6.18/6.38       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 6.18/6.38  thf('127', plain,
% 6.18/6.38      (![X48 : $i]:
% 6.18/6.38         (m1_subset_1 @ (k6_partfun1 @ X48) @ 
% 6.18/6.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))),
% 6.18/6.38      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 6.18/6.38  thf('128', plain,
% 6.18/6.38      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 6.18/6.38      inference('sup+', [status(thm)], ['126', '127'])).
% 6.18/6.38  thf('129', plain,
% 6.18/6.38      (![X20 : $i, X21 : $i]:
% 6.18/6.38         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 6.18/6.38      inference('cnf', [status(esa)], [t3_subset])).
% 6.18/6.38  thf('130', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 6.18/6.38      inference('sup-', [status(thm)], ['128', '129'])).
% 6.18/6.38  thf('131', plain,
% 6.18/6.38      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['15', '16'])).
% 6.18/6.38  thf('132', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['130', '131'])).
% 6.18/6.38  thf('133', plain, (![X47 : $i]: (v1_partfun1 @ (k6_partfun1 @ X47) @ X47)),
% 6.18/6.38      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 6.18/6.38  thf('134', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 6.18/6.38      inference('sup+', [status(thm)], ['132', '133'])).
% 6.18/6.38  thf(d4_partfun1, axiom,
% 6.18/6.38    (![A:$i,B:$i]:
% 6.18/6.38     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 6.18/6.38       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 6.18/6.38  thf('135', plain,
% 6.18/6.38      (![X45 : $i, X46 : $i]:
% 6.18/6.38         (~ (v1_partfun1 @ X46 @ X45)
% 6.18/6.38          | ((k1_relat_1 @ X46) = (X45))
% 6.18/6.38          | ~ (v4_relat_1 @ X46 @ X45)
% 6.18/6.38          | ~ (v1_relat_1 @ X46))),
% 6.18/6.38      inference('cnf', [status(esa)], [d4_partfun1])).
% 6.18/6.38  thf('136', plain,
% 6.18/6.38      ((~ (v1_relat_1 @ k1_xboole_0)
% 6.18/6.38        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 6.18/6.38        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 6.18/6.38      inference('sup-', [status(thm)], ['134', '135'])).
% 6.18/6.38  thf('137', plain,
% 6.18/6.38      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 6.18/6.38      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.38  thf(cc1_relset_1, axiom,
% 6.18/6.38    (![A:$i,B:$i,C:$i]:
% 6.18/6.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.18/6.38       ( v1_relat_1 @ C ) ))).
% 6.18/6.38  thf('138', plain,
% 6.18/6.38      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.18/6.38         ((v1_relat_1 @ X26)
% 6.18/6.38          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 6.18/6.38      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.18/6.38  thf('139', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.18/6.38      inference('sup-', [status(thm)], ['137', '138'])).
% 6.18/6.38  thf('140', plain,
% 6.18/6.38      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 6.18/6.38      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.38  thf(cc2_relset_1, axiom,
% 6.18/6.38    (![A:$i,B:$i,C:$i]:
% 6.18/6.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.18/6.38       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.18/6.38  thf('141', plain,
% 6.18/6.38      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.18/6.38         ((v4_relat_1 @ X29 @ X30)
% 6.18/6.38          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 6.18/6.38      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.18/6.38  thf('142', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 6.18/6.38      inference('sup-', [status(thm)], ['140', '141'])).
% 6.18/6.38  thf('143', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.18/6.38      inference('demod', [status(thm)], ['136', '139', '142'])).
% 6.18/6.38  thf('144', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.18/6.38      inference('demod', [status(thm)], ['125', '143'])).
% 6.18/6.38  thf('145', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.18/6.38      inference('demod', [status(thm)], ['122', '144'])).
% 6.18/6.38  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('147', plain,
% 6.18/6.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['5', '6'])).
% 6.18/6.38  thf('148', plain,
% 6.18/6.38      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 6.18/6.38      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.38  thf('149', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('sup+', [status(thm)], ['147', '148'])).
% 6.18/6.38  thf(t18_tdlat_3, axiom,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.18/6.38       ( ( v1_tdlat_3 @ A ) <=>
% 6.18/6.38         ( ![B:$i]:
% 6.18/6.38           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.18/6.38             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 6.18/6.38  thf('150', plain,
% 6.18/6.38      (![X74 : $i, X75 : $i]:
% 6.18/6.38         (~ (v1_tdlat_3 @ X74)
% 6.18/6.38          | (v4_pre_topc @ X75 @ X74)
% 6.18/6.38          | ~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (u1_struct_0 @ X74)))
% 6.18/6.38          | ~ (l1_pre_topc @ X74)
% 6.18/6.38          | ~ (v2_pre_topc @ X74))),
% 6.18/6.38      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 6.18/6.38  thf('151', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         (~ (v1_xboole_0 @ X1)
% 6.18/6.38          | ~ (v2_pre_topc @ X0)
% 6.18/6.38          | ~ (l1_pre_topc @ X0)
% 6.18/6.38          | (v4_pre_topc @ X1 @ X0)
% 6.18/6.38          | ~ (v1_tdlat_3 @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['149', '150'])).
% 6.18/6.38  thf('152', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         (~ (v1_tdlat_3 @ sk_A)
% 6.18/6.38          | (v4_pre_topc @ X0 @ sk_A)
% 6.18/6.38          | ~ (v2_pre_topc @ sk_A)
% 6.18/6.38          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['146', '151'])).
% 6.18/6.38  thf('153', plain, ((v1_tdlat_3 @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('155', plain,
% 6.18/6.38      (![X0 : $i]: ((v4_pre_topc @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('demod', [status(thm)], ['152', '153', '154'])).
% 6.18/6.38  thf('156', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('sup+', [status(thm)], ['147', '148'])).
% 6.18/6.38  thf(t52_pre_topc, axiom,
% 6.18/6.38    (![A:$i]:
% 6.18/6.38     ( ( l1_pre_topc @ A ) =>
% 6.18/6.38       ( ![B:$i]:
% 6.18/6.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.18/6.38           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 6.18/6.38             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 6.18/6.38               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 6.18/6.38  thf('157', plain,
% 6.18/6.38      (![X51 : $i, X52 : $i]:
% 6.18/6.38         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 6.18/6.38          | ~ (v4_pre_topc @ X51 @ X52)
% 6.18/6.38          | ((k2_pre_topc @ X52 @ X51) = (X51))
% 6.18/6.38          | ~ (l1_pre_topc @ X52))),
% 6.18/6.38      inference('cnf', [status(esa)], [t52_pre_topc])).
% 6.18/6.38  thf('158', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         (~ (v1_xboole_0 @ X1)
% 6.18/6.38          | ~ (l1_pre_topc @ X0)
% 6.18/6.38          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 6.18/6.38          | ~ (v4_pre_topc @ X1 @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['156', '157'])).
% 6.18/6.38  thf('159', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         (~ (v1_xboole_0 @ X0)
% 6.18/6.38          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 6.18/6.38          | ~ (l1_pre_topc @ sk_A)
% 6.18/6.38          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['155', '158'])).
% 6.18/6.38  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('161', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         (~ (v1_xboole_0 @ X0)
% 6.18/6.38          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 6.18/6.38          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('demod', [status(thm)], ['159', '160'])).
% 6.18/6.38  thf('162', plain,
% 6.18/6.38      (![X0 : $i]: (((k2_pre_topc @ sk_A @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.38      inference('simplify', [status(thm)], ['161'])).
% 6.18/6.38  thf('163', plain,
% 6.18/6.38      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 6.18/6.38      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.38  thf('164', plain,
% 6.18/6.38      (![X51 : $i, X52 : $i]:
% 6.18/6.38         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 6.18/6.38          | ~ (v2_pre_topc @ X52)
% 6.18/6.38          | ((k2_pre_topc @ X52 @ X51) != (X51))
% 6.18/6.38          | (v4_pre_topc @ X51 @ X52)
% 6.18/6.38          | ~ (l1_pre_topc @ X52))),
% 6.18/6.38      inference('cnf', [status(esa)], [t52_pre_topc])).
% 6.18/6.38  thf('165', plain,
% 6.18/6.38      (![X0 : $i]:
% 6.18/6.38         (~ (l1_pre_topc @ X0)
% 6.18/6.38          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 6.18/6.38          | ((k2_pre_topc @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 6.18/6.38          | ~ (v2_pre_topc @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['163', '164'])).
% 6.18/6.38  thf('166', plain,
% 6.18/6.38      ((((k1_xboole_0) != (k1_xboole_0))
% 6.18/6.38        | ~ (v1_xboole_0 @ k1_xboole_0)
% 6.18/6.38        | ~ (v2_pre_topc @ sk_A)
% 6.18/6.38        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 6.18/6.38        | ~ (l1_pre_topc @ sk_A))),
% 6.18/6.38      inference('sup-', [status(thm)], ['162', '165'])).
% 6.18/6.38  thf('167', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.38  thf('168', plain, ((v2_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('170', plain,
% 6.18/6.38      ((((k1_xboole_0) != (k1_xboole_0)) | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 6.18/6.38      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 6.18/6.38  thf('171', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 6.18/6.38      inference('simplify', [status(thm)], ['170'])).
% 6.18/6.38  thf('172', plain,
% 6.18/6.38      (![X0 : $i, X1 : $i]:
% 6.18/6.38         (~ (v1_xboole_0 @ X1)
% 6.18/6.38          | ~ (l1_pre_topc @ X0)
% 6.18/6.38          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 6.18/6.38          | ~ (v4_pre_topc @ X1 @ X0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['156', '157'])).
% 6.18/6.38  thf('173', plain,
% 6.18/6.38      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 6.18/6.38        | ~ (l1_pre_topc @ sk_A)
% 6.18/6.38        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['171', '172'])).
% 6.18/6.38  thf('174', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('175', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.38  thf('176', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 6.18/6.38      inference('demod', [status(thm)], ['173', '174', '175'])).
% 6.18/6.38  thf('177', plain, (((u1_struct_0 @ sk_B_2) = (k1_xboole_0))),
% 6.18/6.38      inference('clc', [status(thm)], ['116', '117'])).
% 6.18/6.38  thf('178', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 6.18/6.38      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.18/6.38  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('181', plain, ((v1_funct_1 @ sk_C_1)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('182', plain, (((sk_C_1) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['37', '52'])).
% 6.18/6.38  thf('183', plain, ((v1_funct_1 @ k1_xboole_0)),
% 6.18/6.38      inference('demod', [status(thm)], ['181', '182'])).
% 6.18/6.38  thf('184', plain, (((u1_struct_0 @ sk_B_2) = (k1_xboole_0))),
% 6.18/6.38      inference('clc', [status(thm)], ['116', '117'])).
% 6.18/6.38  thf('185', plain,
% 6.18/6.38      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('186', plain, (((sk_C_1) = (k1_xboole_0))),
% 6.18/6.38      inference('sup-', [status(thm)], ['37', '52'])).
% 6.18/6.38  thf('187', plain,
% 6.18/6.38      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 6.18/6.38        (u1_struct_0 @ sk_B_2))),
% 6.18/6.38      inference('demod', [status(thm)], ['185', '186'])).
% 6.18/6.38  thf('188', plain, (((u1_struct_0 @ sk_B_2) = (k1_xboole_0))),
% 6.18/6.38      inference('clc', [status(thm)], ['116', '117'])).
% 6.18/6.38  thf('189', plain,
% 6.18/6.38      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 6.18/6.38      inference('demod', [status(thm)], ['187', '188'])).
% 6.18/6.38  thf('190', plain, (((u1_struct_0 @ sk_B_2) = (k1_xboole_0))),
% 6.18/6.38      inference('clc', [status(thm)], ['116', '117'])).
% 6.18/6.38  thf('191', plain,
% 6.18/6.38      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 6.18/6.38      inference('simplify', [status(thm)], ['8'])).
% 6.18/6.38  thf('192', plain,
% 6.18/6.38      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 6.18/6.38      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.38  thf('193', plain, ((l1_pre_topc @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('194', plain, ((v2_pre_topc @ sk_B_2)),
% 6.18/6.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.38  thf('195', plain, ((v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 6.18/6.38      inference('demod', [status(thm)],
% 6.18/6.38                ['97', '118', '119', '145', '176', '177', '178', '179', '180', 
% 6.18/6.38                 '183', '184', '189', '190', '191', '192', '193', '194'])).
% 6.18/6.38  thf('196', plain, ($false), inference('demod', [status(thm)], ['54', '195'])).
% 6.18/6.38  
% 6.18/6.38  % SZS output end Refutation
% 6.18/6.38  
% 6.18/6.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
