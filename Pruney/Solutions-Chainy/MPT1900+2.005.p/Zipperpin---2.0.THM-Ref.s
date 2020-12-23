%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8tw306Q5HQ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:44 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  229 (1644 expanded)
%              Number of leaves         :   64 ( 536 expanded)
%              Depth                    :   15
%              Number of atoms          : 1612 (22793 expanded)
%              Number of equality atoms :   75 ( 322 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 )
      | ~ ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ~ ( v2_struct_0 @ sk_B_3 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X41: $i] :
      ( ( l1_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v2_struct_0 @ sk_B_3 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','15','16','19'])).

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

thf('21',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( ( k2_struct_0 @ X46 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X43: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
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

thf('27',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( zip_tseitin_0 @ X57 @ X58 )
      | ( zip_tseitin_2 @ X59 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X57 ) ) ) )
      | ~ ( v1_funct_2 @ X59 @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X57 ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,
    ( ~ ( l1_struct_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_B_3 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B_3 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('40',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( v1_tdlat_3 @ X65 )
      | ( v3_pre_topc @ X66 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X65 )
      | ~ ( v2_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X48: $i,X49: $i,X51: $i,X52: $i] :
      ( ( zip_tseitin_1 @ X48 @ X51 @ X49 @ X52 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X49 ) @ X51 @ X48 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X53 @ X54 @ X55 ) @ X55 @ X54 @ X53 )
      | ( v5_pre_topc @ X55 @ X53 @ X54 )
      | ~ ( zip_tseitin_2 @ X55 @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    v2_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','52'])).

thf('54',plain,(
    ~ ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ) ),
    inference(demod,[status(thm)],['0','53'])).

thf('55',plain,(
    ! [X42: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 )
      | ~ ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
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

thf('57',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( v2_pre_topc @ X60 )
      | ~ ( l1_pre_topc @ X60 )
      | ( m1_subset_1 @ ( sk_D_1 @ X61 @ X60 @ X62 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( v5_pre_topc @ X61 @ X62 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X62 ) @ ( u1_struct_0 @ X60 ) ) ) )
      | ~ ( v1_funct_2 @ X61 @ ( u1_struct_0 @ X62 ) @ ( u1_struct_0 @ X60 ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( l1_pre_topc @ X62 )
      | ~ ( v2_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('58',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_pre_topc @ sk_B_3 )
    | ~ ( v2_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64'])).

thf('66',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = ( u1_struct_0 @ sk_B_3 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,
    ( ~ ( v2_struct_0 @ sk_B_3 )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['55','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('78',plain,
    ( ~ ( v2_struct_0 @ sk_B_3 )
    | ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    v2_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['36','51'])).

thf('80',plain,
    ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
    = ( u1_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','52'])).

thf('82',plain,
    ( ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    = ( u1_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( v2_pre_topc @ X60 )
      | ~ ( l1_pre_topc @ X60 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X62 @ ( k8_relset_1 @ ( u1_struct_0 @ X62 ) @ ( u1_struct_0 @ X60 ) @ X61 @ ( sk_D_1 @ X61 @ X60 @ X62 ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X62 ) @ ( u1_struct_0 @ X60 ) @ X61 @ ( k2_pre_topc @ X60 @ ( sk_D_1 @ X61 @ X60 @ X62 ) ) ) )
      | ( v5_pre_topc @ X61 @ X62 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X62 ) @ ( u1_struct_0 @ X60 ) ) ) )
      | ~ ( v1_funct_2 @ X61 @ ( u1_struct_0 @ X62 ) @ ( u1_struct_0 @ X60 ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( l1_pre_topc @ X62 )
      | ~ ( v2_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('84',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ k1_xboole_0 @ ( k2_pre_topc @ sk_B_3 @ ( u1_struct_0 @ sk_B_3 ) ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) )
    | ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 )
    | ~ ( l1_pre_topc @ sk_B_3 )
    | ~ ( v2_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    = ( u1_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('86',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('87',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k8_relset_1 @ X38 @ X39 @ X40 @ X39 )
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('90',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('92',plain,(
    ! [X27: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X27 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('93',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v4_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('96',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('97',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('98',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['94','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('101',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k8_relset_1 @ X38 @ X39 @ X40 @ X39 )
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('106',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('109',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('112',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

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

thf('113',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v4_pre_topc @ X44 @ X45 )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = X44 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('114',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v4_pre_topc @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v4_pre_topc @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('118',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v1_tdlat_3 @ X67 )
      | ( v4_pre_topc @ X68 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X67 )
      | ~ ( v2_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('119',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k1_relat_1 @ sk_C_1 ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v4_pre_topc @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['116','123'])).

thf('125',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','52'])).

thf('126',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('127',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','52'])).

thf('128',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('129',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','52'])).

thf('135',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('137',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ) ),
    inference(demod,[status(thm)],['84','85','103','129','130','131','132','135','136','137','138'])).

thf('140',plain,
    ( ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    = ( u1_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('141',plain,(
    ! [X42: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 )
      | ~ ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('142',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('144',plain,
    ( ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v2_struct_0 @ sk_B_3 )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('147',plain,
    ( ~ ( v2_struct_0 @ sk_B_3 )
    | ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    v2_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['36','51'])).

thf('149',plain,
    ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','52'])).

thf('151',plain,
    ( ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['140','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('154',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ~ ( v2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('157',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( v2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    v2_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['36','51'])).

thf('159',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','52'])).

thf('161',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ),
    inference(demod,[status(thm)],['139','152','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['54','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8tw306Q5HQ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.80/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/1.00  % Solved by: fo/fo7.sh
% 0.80/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.00  % done 765 iterations in 0.551s
% 0.80/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/1.00  % SZS output start Refutation
% 0.80/1.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.80/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.80/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.00  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.80/1.00  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.80/1.00  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.80/1.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.80/1.00  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.80/1.00  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.80/1.00  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.80/1.00  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.80/1.00  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.80/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.00  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.80/1.00  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.80/1.00  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.80/1.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.80/1.00  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.80/1.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.80/1.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.80/1.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.80/1.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.80/1.00  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.80/1.00  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.80/1.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.80/1.00  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.80/1.00  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.80/1.00  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.80/1.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.80/1.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.80/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.00  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.80/1.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.80/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.00  thf(t68_tex_2, conjecture,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( ( v1_funct_1 @ C ) & 
% 0.80/1.00                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.80/1.00                 ( m1_subset_1 @
% 0.80/1.00                   C @ 
% 0.80/1.00                   ( k1_zfmisc_1 @
% 0.80/1.00                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.80/1.00               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 0.80/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.00    (~( ![A:$i]:
% 0.80/1.00        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00          ( ![B:$i]:
% 0.80/1.00            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.80/1.00              ( ![C:$i]:
% 0.80/1.00                ( ( ( v1_funct_1 @ C ) & 
% 0.80/1.00                    ( v1_funct_2 @
% 0.80/1.00                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.80/1.00                    ( m1_subset_1 @
% 0.80/1.00                      C @ 
% 0.80/1.00                      ( k1_zfmisc_1 @
% 0.80/1.00                        ( k2_zfmisc_1 @
% 0.80/1.00                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.80/1.00                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 0.80/1.00    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 0.80/1.00  thf('0', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(fc1_struct_0, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.80/1.00       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.80/1.00  thf('1', plain,
% 0.80/1.00      (![X42 : $i]:
% 0.80/1.00         ((v1_xboole_0 @ (u1_struct_0 @ X42))
% 0.80/1.00          | ~ (l1_struct_0 @ X42)
% 0.80/1.00          | ~ (v2_struct_0 @ X42))),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.80/1.00  thf(l13_xboole_0, axiom,
% 0.80/1.00    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.80/1.00  thf('2', plain,
% 0.80/1.00      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf('3', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (v2_struct_0 @ X0)
% 0.80/1.00          | ~ (l1_struct_0 @ X0)
% 0.80/1.00          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.00  thf('4', plain,
% 0.80/1.00      ((m1_subset_1 @ sk_C_1 @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(t3_subset, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.80/1.00  thf('5', plain,
% 0.80/1.00      (![X16 : $i, X17 : $i]:
% 0.80/1.00         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.00  thf('6', plain,
% 0.80/1.00      ((r1_tarski @ sk_C_1 @ 
% 0.80/1.00        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['4', '5'])).
% 0.80/1.00  thf('7', plain,
% 0.80/1.00      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.80/1.00  thf('8', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.80/1.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.80/1.00  thf(d10_xboole_0, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.80/1.00  thf('9', plain,
% 0.80/1.00      (![X8 : $i, X10 : $i]:
% 0.80/1.00         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.80/1.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.00  thf('10', plain,
% 0.80/1.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.00  thf('11', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (r1_tarski @ X1 @ X0)
% 0.80/1.00          | ~ (v1_xboole_0 @ X0)
% 0.80/1.00          | ((X1) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['7', '10'])).
% 0.80/1.00  thf('12', plain,
% 0.80/1.00      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.00        | ~ (v1_xboole_0 @ 
% 0.80/1.00             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.80/1.00      inference('sup-', [status(thm)], ['6', '11'])).
% 0.80/1.00  thf('13', plain,
% 0.80/1.00      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.80/1.00        | ~ (l1_struct_0 @ sk_B_3)
% 0.80/1.00        | ~ (v2_struct_0 @ sk_B_3)
% 0.80/1.00        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['3', '12'])).
% 0.80/1.00  thf(t113_zfmisc_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.80/1.00       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.80/1.00  thf('14', plain,
% 0.80/1.00      (![X13 : $i, X14 : $i]:
% 0.80/1.00         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.80/1.00          | ((X14) != (k1_xboole_0)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.80/1.00  thf('15', plain,
% 0.80/1.00      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['14'])).
% 0.80/1.00  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.80/1.00  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('17', plain, ((l1_pre_topc @ sk_B_3)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(dt_l1_pre_topc, axiom,
% 0.80/1.00    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.80/1.00  thf('18', plain,
% 0.80/1.00      (![X41 : $i]: ((l1_struct_0 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.80/1.00  thf('19', plain, ((l1_struct_0 @ sk_B_3)),
% 0.80/1.00      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.00  thf('20', plain, ((~ (v2_struct_0 @ sk_B_3) | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['13', '15', '16', '19'])).
% 0.80/1.00  thf(t55_tops_2, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( l1_pre_topc @ A ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( l1_pre_topc @ B ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( ( m1_subset_1 @
% 0.80/1.00                   C @ 
% 0.80/1.00                   ( k1_zfmisc_1 @
% 0.80/1.00                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.80/1.00                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.80/1.00                 ( v1_funct_1 @ C ) ) =>
% 0.80/1.00               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.80/1.00                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.80/1.00                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.80/1.00                   ( ![D:$i]:
% 0.80/1.00                     ( ( m1_subset_1 @
% 0.80/1.00                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.80/1.00                       ( ( v3_pre_topc @ D @ B ) =>
% 0.80/1.00                         ( v3_pre_topc @
% 0.80/1.00                           ( k8_relset_1 @
% 0.80/1.00                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.80/1.00                           A ) ) ) ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf(zf_stmt_1, axiom,
% 0.80/1.00    (![B:$i,A:$i]:
% 0.80/1.00     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.80/1.00         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.80/1.00       ( zip_tseitin_0 @ B @ A ) ))).
% 0.80/1.00  thf('21', plain,
% 0.80/1.00      (![X46 : $i, X47 : $i]:
% 0.80/1.00         ((zip_tseitin_0 @ X46 @ X47) | ((k2_struct_0 @ X46) = (k1_xboole_0)))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.80/1.00  thf(fc5_struct_0, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.80/1.00       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.80/1.00  thf('22', plain,
% 0.80/1.00      (![X43 : $i]:
% 0.80/1.00         (~ (v1_xboole_0 @ (k2_struct_0 @ X43))
% 0.80/1.00          | ~ (l1_struct_0 @ X43)
% 0.80/1.00          | (v2_struct_0 @ X43))),
% 0.80/1.00      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.80/1.00  thf('23', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.80/1.00          | (zip_tseitin_0 @ X0 @ X1)
% 0.80/1.00          | (v2_struct_0 @ X0)
% 0.80/1.00          | ~ (l1_struct_0 @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['21', '22'])).
% 0.80/1.00  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('25', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((zip_tseitin_0 @ X0 @ X1) | (v2_struct_0 @ X0) | ~ (l1_struct_0 @ X0))),
% 0.80/1.00      inference('demod', [status(thm)], ['23', '24'])).
% 0.80/1.00  thf('26', plain,
% 0.80/1.00      ((m1_subset_1 @ sk_C_1 @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.80/1.00  thf(zf_stmt_3, axiom,
% 0.80/1.00    (![C:$i,B:$i,A:$i]:
% 0.80/1.00     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.80/1.00       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.80/1.00         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 0.80/1.00  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.80/1.00  thf(zf_stmt_5, axiom,
% 0.80/1.00    (![D:$i,C:$i,B:$i,A:$i]:
% 0.80/1.00     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.80/1.00       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.80/1.00         ( ( v3_pre_topc @ D @ B ) =>
% 0.80/1.00           ( v3_pre_topc @
% 0.80/1.00             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.80/1.00             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 0.80/1.00  thf(zf_stmt_7, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( l1_pre_topc @ A ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( l1_pre_topc @ B ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( ( v1_funct_1 @ C ) & 
% 0.80/1.00                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.80/1.00                 ( m1_subset_1 @
% 0.80/1.00                   C @ 
% 0.80/1.00                   ( k1_zfmisc_1 @
% 0.80/1.00                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.80/1.00               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 0.80/1.00  thf('27', plain,
% 0.80/1.00      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.80/1.00         (~ (l1_pre_topc @ X57)
% 0.80/1.00          | ~ (zip_tseitin_0 @ X57 @ X58)
% 0.80/1.00          | (zip_tseitin_2 @ X59 @ X57 @ X58)
% 0.80/1.00          | ~ (m1_subset_1 @ X59 @ 
% 0.80/1.00               (k1_zfmisc_1 @ 
% 0.80/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X57))))
% 0.80/1.00          | ~ (v1_funct_2 @ X59 @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X57))
% 0.80/1.00          | ~ (v1_funct_1 @ X59)
% 0.80/1.00          | ~ (l1_pre_topc @ X58))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.80/1.00  thf('28', plain,
% 0.80/1.00      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | ~ (v1_funct_1 @ sk_C_1)
% 0.80/1.00        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (u1_struct_0 @ sk_B_3))
% 0.80/1.00        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 0.80/1.00        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_B_3))),
% 0.80/1.00      inference('sup-', [status(thm)], ['26', '27'])).
% 0.80/1.00  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('30', plain, ((v1_funct_1 @ sk_C_1)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('31', plain,
% 0.80/1.00      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('32', plain, ((l1_pre_topc @ sk_B_3)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('33', plain,
% 0.80/1.00      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 0.80/1.00        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.80/1.00  thf('34', plain,
% 0.80/1.00      ((~ (l1_struct_0 @ sk_B_3)
% 0.80/1.00        | (v2_struct_0 @ sk_B_3)
% 0.80/1.00        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['25', '33'])).
% 0.80/1.00  thf('35', plain, ((l1_struct_0 @ sk_B_3)),
% 0.80/1.00      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.00  thf('36', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_B_3) | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['34', '35'])).
% 0.80/1.00  thf('37', plain,
% 0.80/1.00      ((m1_subset_1 @ sk_C_1 @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(dt_k8_relset_1, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/1.00       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.80/1.00  thf('38', plain,
% 0.80/1.00      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.80/1.00          | (m1_subset_1 @ (k8_relset_1 @ X32 @ X33 @ X31 @ X34) @ 
% 0.80/1.00             (k1_zfmisc_1 @ X32)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.80/1.00  thf('39', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (m1_subset_1 @ 
% 0.80/1.00          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00           sk_C_1 @ X0) @ 
% 0.80/1.00          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['37', '38'])).
% 0.80/1.00  thf(t17_tdlat_3, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ( v1_tdlat_3 @ A ) <=>
% 0.80/1.00         ( ![B:$i]:
% 0.80/1.00           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.80/1.00  thf('40', plain,
% 0.80/1.00      (![X65 : $i, X66 : $i]:
% 0.80/1.00         (~ (v1_tdlat_3 @ X65)
% 0.80/1.00          | (v3_pre_topc @ X66 @ X65)
% 0.80/1.00          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 0.80/1.00          | ~ (l1_pre_topc @ X65)
% 0.80/1.00          | ~ (v2_pre_topc @ X65))),
% 0.80/1.00      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.80/1.00  thf('41', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (v2_pre_topc @ sk_A)
% 0.80/1.00          | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00          | (v3_pre_topc @ 
% 0.80/1.00             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00              sk_C_1 @ X0) @ 
% 0.80/1.00             sk_A)
% 0.80/1.00          | ~ (v1_tdlat_3 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['39', '40'])).
% 0.80/1.00  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('44', plain, ((v1_tdlat_3 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('45', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (v3_pre_topc @ 
% 0.80/1.00          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00           sk_C_1 @ X0) @ 
% 0.80/1.00          sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.80/1.00  thf('46', plain,
% 0.80/1.00      (![X48 : $i, X49 : $i, X51 : $i, X52 : $i]:
% 0.80/1.00         ((zip_tseitin_1 @ X48 @ X51 @ X49 @ X52)
% 0.80/1.00          | ~ (v3_pre_topc @ 
% 0.80/1.00               (k8_relset_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X49) @ 
% 0.80/1.00                X51 @ X48) @ 
% 0.80/1.00               X52))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.80/1.00  thf('47', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 0.80/1.00      inference('sup-', [status(thm)], ['45', '46'])).
% 0.80/1.00  thf('48', plain,
% 0.80/1.00      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.80/1.00         (~ (zip_tseitin_1 @ (sk_D @ X53 @ X54 @ X55) @ X55 @ X54 @ X53)
% 0.80/1.00          | (v5_pre_topc @ X55 @ X53 @ X54)
% 0.80/1.00          | ~ (zip_tseitin_2 @ X55 @ X54 @ X53))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.80/1.00  thf('49', plain,
% 0.80/1.00      ((~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 0.80/1.00        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3))),
% 0.80/1.00      inference('sup-', [status(thm)], ['47', '48'])).
% 0.80/1.00  thf('50', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('51', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 0.80/1.00      inference('clc', [status(thm)], ['49', '50'])).
% 0.80/1.00  thf('52', plain, ((v2_struct_0 @ sk_B_3)),
% 0.80/1.00      inference('sup-', [status(thm)], ['36', '51'])).
% 0.80/1.00  thf('53', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.00      inference('demod', [status(thm)], ['20', '52'])).
% 0.80/1.00  thf('54', plain, (~ (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 0.80/1.00      inference('demod', [status(thm)], ['0', '53'])).
% 0.80/1.00  thf('55', plain,
% 0.80/1.00      (![X42 : $i]:
% 0.80/1.00         ((v1_xboole_0 @ (u1_struct_0 @ X42))
% 0.80/1.00          | ~ (l1_struct_0 @ X42)
% 0.80/1.00          | ~ (v2_struct_0 @ X42))),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.80/1.00  thf('56', plain,
% 0.80/1.00      ((m1_subset_1 @ sk_C_1 @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(t56_tops_2, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( ( v1_funct_1 @ C ) & 
% 0.80/1.00                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.80/1.00                 ( m1_subset_1 @
% 0.80/1.00                   C @ 
% 0.80/1.00                   ( k1_zfmisc_1 @
% 0.80/1.00                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.80/1.00               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.80/1.00                 ( ![D:$i]:
% 0.80/1.00                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.80/1.00                     ( r1_tarski @
% 0.80/1.00                       ( k2_pre_topc @
% 0.80/1.00                         A @ 
% 0.80/1.00                         ( k8_relset_1 @
% 0.80/1.00                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 0.80/1.00                       ( k8_relset_1 @
% 0.80/1.00                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.80/1.00                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf('57', plain,
% 0.80/1.00      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.80/1.00         (~ (v2_pre_topc @ X60)
% 0.80/1.00          | ~ (l1_pre_topc @ X60)
% 0.80/1.00          | (m1_subset_1 @ (sk_D_1 @ X61 @ X60 @ X62) @ 
% 0.80/1.00             (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 0.80/1.00          | (v5_pre_topc @ X61 @ X62 @ X60)
% 0.80/1.00          | ~ (m1_subset_1 @ X61 @ 
% 0.80/1.00               (k1_zfmisc_1 @ 
% 0.80/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X62) @ (u1_struct_0 @ X60))))
% 0.80/1.00          | ~ (v1_funct_2 @ X61 @ (u1_struct_0 @ X62) @ (u1_struct_0 @ X60))
% 0.80/1.00          | ~ (v1_funct_1 @ X61)
% 0.80/1.00          | ~ (l1_pre_topc @ X62)
% 0.80/1.00          | ~ (v2_pre_topc @ X62))),
% 0.80/1.00      inference('cnf', [status(esa)], [t56_tops_2])).
% 0.80/1.00  thf('58', plain,
% 0.80/1.00      ((~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | ~ (v1_funct_1 @ sk_C_1)
% 0.80/1.00        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (u1_struct_0 @ sk_B_3))
% 0.80/1.00        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)
% 0.80/1.00        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 0.80/1.00           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))
% 0.80/1.00        | ~ (l1_pre_topc @ sk_B_3)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_B_3))),
% 0.80/1.00      inference('sup-', [status(thm)], ['56', '57'])).
% 0.80/1.00  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('62', plain,
% 0.80/1.00      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('63', plain, ((l1_pre_topc @ sk_B_3)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('64', plain, ((v2_pre_topc @ sk_B_3)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('65', plain,
% 0.80/1.00      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)
% 0.80/1.00        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 0.80/1.00           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3))))),
% 0.80/1.00      inference('demod', [status(thm)],
% 0.80/1.00                ['58', '59', '60', '61', '62', '63', '64'])).
% 0.80/1.00  thf('66', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('67', plain,
% 0.80/1.00      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 0.80/1.00      inference('clc', [status(thm)], ['65', '66'])).
% 0.80/1.00  thf('68', plain,
% 0.80/1.00      (![X16 : $i, X17 : $i]:
% 0.80/1.00         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.00  thf('69', plain,
% 0.80/1.00      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 0.80/1.00      inference('sup-', [status(thm)], ['67', '68'])).
% 0.80/1.00  thf('70', plain,
% 0.80/1.00      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf('71', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.80/1.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.80/1.00  thf('72', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['70', '71'])).
% 0.80/1.00  thf('73', plain,
% 0.80/1.00      (![X8 : $i, X10 : $i]:
% 0.80/1.00         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.80/1.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.00  thf('74', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['72', '73'])).
% 0.80/1.00  thf('75', plain,
% 0.80/1.00      ((((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3))
% 0.80/1.00        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['69', '74'])).
% 0.80/1.00  thf('76', plain,
% 0.80/1.00      ((~ (v2_struct_0 @ sk_B_3)
% 0.80/1.00        | ~ (l1_struct_0 @ sk_B_3)
% 0.80/1.00        | ((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['55', '75'])).
% 0.80/1.00  thf('77', plain, ((l1_struct_0 @ sk_B_3)),
% 0.80/1.00      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.00  thf('78', plain,
% 0.80/1.00      ((~ (v2_struct_0 @ sk_B_3)
% 0.80/1.00        | ((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3)))),
% 0.80/1.00      inference('demod', [status(thm)], ['76', '77'])).
% 0.80/1.00  thf('79', plain, ((v2_struct_0 @ sk_B_3)),
% 0.80/1.00      inference('sup-', [status(thm)], ['36', '51'])).
% 0.80/1.00  thf('80', plain,
% 0.80/1.00      (((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3))),
% 0.80/1.00      inference('demod', [status(thm)], ['78', '79'])).
% 0.80/1.00  thf('81', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.00      inference('demod', [status(thm)], ['20', '52'])).
% 0.80/1.00  thf('82', plain,
% 0.80/1.00      (((sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3))),
% 0.80/1.00      inference('demod', [status(thm)], ['80', '81'])).
% 0.80/1.00  thf('83', plain,
% 0.80/1.00      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.80/1.00         (~ (v2_pre_topc @ X60)
% 0.80/1.00          | ~ (l1_pre_topc @ X60)
% 0.80/1.00          | ~ (r1_tarski @ 
% 0.80/1.00               (k2_pre_topc @ X62 @ 
% 0.80/1.00                (k8_relset_1 @ (u1_struct_0 @ X62) @ (u1_struct_0 @ X60) @ 
% 0.80/1.00                 X61 @ (sk_D_1 @ X61 @ X60 @ X62))) @ 
% 0.80/1.00               (k8_relset_1 @ (u1_struct_0 @ X62) @ (u1_struct_0 @ X60) @ 
% 0.80/1.00                X61 @ (k2_pre_topc @ X60 @ (sk_D_1 @ X61 @ X60 @ X62))))
% 0.80/1.00          | (v5_pre_topc @ X61 @ X62 @ X60)
% 0.80/1.00          | ~ (m1_subset_1 @ X61 @ 
% 0.80/1.00               (k1_zfmisc_1 @ 
% 0.80/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X62) @ (u1_struct_0 @ X60))))
% 0.80/1.00          | ~ (v1_funct_2 @ X61 @ (u1_struct_0 @ X62) @ (u1_struct_0 @ X60))
% 0.80/1.00          | ~ (v1_funct_1 @ X61)
% 0.80/1.00          | ~ (l1_pre_topc @ X62)
% 0.80/1.00          | ~ (v2_pre_topc @ X62))),
% 0.80/1.00      inference('cnf', [status(esa)], [t56_tops_2])).
% 0.80/1.00  thf('84', plain,
% 0.80/1.00      ((~ (r1_tarski @ 
% 0.80/1.00           (k2_pre_topc @ sk_A @ 
% 0.80/1.00            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00             k1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))) @ 
% 0.80/1.00           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00            k1_xboole_0 @ (k2_pre_topc @ sk_B_3 @ (u1_struct_0 @ sk_B_3))))
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.80/1.00        | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (u1_struct_0 @ sk_B_3))
% 0.80/1.00        | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.80/1.00             (k1_zfmisc_1 @ 
% 0.80/1.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))
% 0.80/1.00        | (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_B_3)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_B_3))),
% 0.80/1.00      inference('sup-', [status(thm)], ['82', '83'])).
% 0.80/1.00  thf('85', plain,
% 0.80/1.00      (((sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3))),
% 0.80/1.00      inference('demod', [status(thm)], ['80', '81'])).
% 0.80/1.00  thf(t4_subset_1, axiom,
% 0.80/1.00    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.80/1.00  thf('86', plain,
% 0.80/1.00      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.80/1.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.80/1.00  thf(t38_relset_1, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i]:
% 0.80/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/1.00       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.80/1.00         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.80/1.00  thf('87', plain,
% 0.80/1.00      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.80/1.00         (((k8_relset_1 @ X38 @ X39 @ X40 @ X39)
% 0.80/1.00            = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.80/1.00          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.80/1.00      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.80/1.00  thf('88', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 0.80/1.00           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['86', '87'])).
% 0.80/1.00  thf('89', plain,
% 0.80/1.00      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.80/1.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.80/1.00  thf(redefinition_k1_relset_1, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i]:
% 0.80/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/1.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.80/1.00  thf('90', plain,
% 0.80/1.00      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.80/1.00         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.80/1.00          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.80/1.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.80/1.00  thf('91', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['89', '90'])).
% 0.80/1.00  thf(l222_relat_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.80/1.00  thf('92', plain, (![X27 : $i]: (v4_relat_1 @ k1_xboole_0 @ X27)),
% 0.80/1.00      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.80/1.00  thf(d18_relat_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( v1_relat_1 @ B ) =>
% 0.80/1.00       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.80/1.00  thf('93', plain,
% 0.80/1.00      (![X22 : $i, X23 : $i]:
% 0.80/1.00         (~ (v4_relat_1 @ X22 @ X23)
% 0.80/1.00          | (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.80/1.00          | ~ (v1_relat_1 @ X22))),
% 0.80/1.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.80/1.00  thf('94', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (v1_relat_1 @ k1_xboole_0)
% 0.80/1.00          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['92', '93'])).
% 0.80/1.00  thf('95', plain,
% 0.80/1.00      (![X13 : $i, X14 : $i]:
% 0.80/1.00         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.80/1.00          | ((X13) != (k1_xboole_0)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.80/1.00  thf('96', plain,
% 0.80/1.00      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['95'])).
% 0.80/1.00  thf(fc6_relat_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.80/1.00  thf('97', plain,
% 0.80/1.00      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.80/1.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.80/1.00  thf('98', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.80/1.00      inference('sup+', [status(thm)], ['96', '97'])).
% 0.80/1.00  thf('99', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.80/1.00      inference('demod', [status(thm)], ['94', '98'])).
% 0.80/1.00  thf('100', plain,
% 0.80/1.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.00  thf('101', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['99', '100'])).
% 0.80/1.00  thf('102', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('demod', [status(thm)], ['91', '101'])).
% 0.80/1.00  thf('103', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.80/1.00      inference('demod', [status(thm)], ['88', '102'])).
% 0.80/1.00  thf('104', plain,
% 0.80/1.00      ((m1_subset_1 @ sk_C_1 @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('105', plain,
% 0.80/1.00      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.80/1.00         (((k8_relset_1 @ X38 @ X39 @ X40 @ X39)
% 0.80/1.00            = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.80/1.00          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.80/1.00      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.80/1.00  thf('106', plain,
% 0.80/1.00      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00         sk_C_1 @ (u1_struct_0 @ sk_B_3))
% 0.80/1.00         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00            sk_C_1))),
% 0.80/1.00      inference('sup-', [status(thm)], ['104', '105'])).
% 0.80/1.00  thf('107', plain,
% 0.80/1.00      ((m1_subset_1 @ sk_C_1 @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('108', plain,
% 0.80/1.00      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.80/1.00         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.80/1.00          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.80/1.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.80/1.00  thf('109', plain,
% 0.80/1.00      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 0.80/1.00         = (k1_relat_1 @ sk_C_1))),
% 0.80/1.00      inference('sup-', [status(thm)], ['107', '108'])).
% 0.80/1.00  thf('110', plain,
% 0.80/1.00      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00         sk_C_1 @ (u1_struct_0 @ sk_B_3)) = (k1_relat_1 @ sk_C_1))),
% 0.80/1.00      inference('demod', [status(thm)], ['106', '109'])).
% 0.80/1.00  thf('111', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (m1_subset_1 @ 
% 0.80/1.00          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.80/1.00           sk_C_1 @ X0) @ 
% 0.80/1.00          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['37', '38'])).
% 0.80/1.00  thf('112', plain,
% 0.80/1.00      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['110', '111'])).
% 0.80/1.00  thf(t52_pre_topc, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( l1_pre_topc @ A ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.80/1.00             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.80/1.00               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.80/1.00  thf('113', plain,
% 0.80/1.00      (![X44 : $i, X45 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.80/1.00          | ~ (v4_pre_topc @ X44 @ X45)
% 0.80/1.00          | ((k2_pre_topc @ X45 @ X44) = (X44))
% 0.80/1.00          | ~ (l1_pre_topc @ X45))),
% 0.80/1.00      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.80/1.00  thf('114', plain,
% 0.80/1.00      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | ((k2_pre_topc @ sk_A @ (k1_relat_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))
% 0.80/1.00        | ~ (v4_pre_topc @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['112', '113'])).
% 0.80/1.00  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('116', plain,
% 0.80/1.00      ((((k2_pre_topc @ sk_A @ (k1_relat_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))
% 0.80/1.00        | ~ (v4_pre_topc @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['114', '115'])).
% 0.80/1.00  thf('117', plain,
% 0.80/1.00      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['110', '111'])).
% 0.80/1.00  thf(t18_tdlat_3, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ( v1_tdlat_3 @ A ) <=>
% 0.80/1.00         ( ![B:$i]:
% 0.80/1.00           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.80/1.00  thf('118', plain,
% 0.80/1.00      (![X67 : $i, X68 : $i]:
% 0.80/1.00         (~ (v1_tdlat_3 @ X67)
% 0.80/1.00          | (v4_pre_topc @ X68 @ X67)
% 0.80/1.00          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 0.80/1.00          | ~ (l1_pre_topc @ X67)
% 0.80/1.00          | ~ (v2_pre_topc @ X67))),
% 0.80/1.00      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 0.80/1.00  thf('119', plain,
% 0.80/1.00      ((~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | (v4_pre_topc @ (k1_relat_1 @ sk_C_1) @ sk_A)
% 0.80/1.00        | ~ (v1_tdlat_3 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['117', '118'])).
% 0.80/1.00  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('122', plain, ((v1_tdlat_3 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('123', plain, ((v4_pre_topc @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.80/1.01      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.80/1.01  thf('124', plain,
% 0.80/1.01      (((k2_pre_topc @ sk_A @ (k1_relat_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))),
% 0.80/1.01      inference('demod', [status(thm)], ['116', '123'])).
% 0.80/1.01  thf('125', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['20', '52'])).
% 0.80/1.01  thf('126', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['99', '100'])).
% 0.80/1.01  thf('127', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['20', '52'])).
% 0.80/1.01  thf('128', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['99', '100'])).
% 0.80/1.01  thf('129', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 0.80/1.01  thf('130', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.80/1.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.80/1.01  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('133', plain, ((v1_funct_1 @ sk_C_1)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('134', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['20', '52'])).
% 0.80/1.01  thf('135', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.80/1.01      inference('demod', [status(thm)], ['133', '134'])).
% 0.80/1.01  thf('136', plain,
% 0.80/1.01      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.80/1.01      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.80/1.01  thf('137', plain, ((l1_pre_topc @ sk_B_3)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('138', plain, ((v2_pre_topc @ sk_B_3)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('139', plain,
% 0.80/1.01      ((~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01           (u1_struct_0 @ sk_B_3))
% 0.80/1.01        | (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3))),
% 0.80/1.01      inference('demod', [status(thm)],
% 0.80/1.01                ['84', '85', '103', '129', '130', '131', '132', '135', '136', 
% 0.80/1.01                 '137', '138'])).
% 0.80/1.01  thf('140', plain,
% 0.80/1.01      (((sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3))),
% 0.80/1.01      inference('demod', [status(thm)], ['80', '81'])).
% 0.80/1.01  thf('141', plain,
% 0.80/1.01      (![X42 : $i]:
% 0.80/1.01         ((v1_xboole_0 @ (u1_struct_0 @ X42))
% 0.80/1.01          | ~ (l1_struct_0 @ X42)
% 0.80/1.01          | ~ (v2_struct_0 @ X42))),
% 0.80/1.01      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.80/1.01  thf('142', plain,
% 0.80/1.01      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 0.80/1.01      inference('sup-', [status(thm)], ['67', '68'])).
% 0.80/1.01  thf('143', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]:
% 0.80/1.01         (~ (r1_tarski @ X1 @ X0)
% 0.80/1.01          | ~ (v1_xboole_0 @ X0)
% 0.80/1.01          | ((X1) = (k1_xboole_0)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['7', '10'])).
% 0.80/1.01  thf('144', plain,
% 0.80/1.01      ((((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (k1_xboole_0))
% 0.80/1.01        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['142', '143'])).
% 0.80/1.01  thf('145', plain,
% 0.80/1.01      ((~ (v2_struct_0 @ sk_B_3)
% 0.80/1.01        | ~ (l1_struct_0 @ sk_B_3)
% 0.80/1.01        | ((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (k1_xboole_0)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['141', '144'])).
% 0.80/1.01  thf('146', plain, ((l1_struct_0 @ sk_B_3)),
% 0.80/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.01  thf('147', plain,
% 0.80/1.01      ((~ (v2_struct_0 @ sk_B_3)
% 0.80/1.01        | ((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (k1_xboole_0)))),
% 0.80/1.01      inference('demod', [status(thm)], ['145', '146'])).
% 0.80/1.01  thf('148', plain, ((v2_struct_0 @ sk_B_3)),
% 0.80/1.01      inference('sup-', [status(thm)], ['36', '51'])).
% 0.80/1.01  thf('149', plain, (((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['147', '148'])).
% 0.80/1.01  thf('150', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['20', '52'])).
% 0.80/1.01  thf('151', plain, (((sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['149', '150'])).
% 0.80/1.01  thf('152', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 0.80/1.01      inference('sup+', [status(thm)], ['140', '151'])).
% 0.80/1.01  thf('153', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (~ (v2_struct_0 @ X0)
% 0.80/1.01          | ~ (l1_struct_0 @ X0)
% 0.80/1.01          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.01  thf('154', plain,
% 0.80/1.01      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('155', plain,
% 0.80/1.01      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.80/1.01        | ~ (l1_struct_0 @ sk_B_3)
% 0.80/1.01        | ~ (v2_struct_0 @ sk_B_3))),
% 0.80/1.01      inference('sup+', [status(thm)], ['153', '154'])).
% 0.80/1.01  thf('156', plain, ((l1_struct_0 @ sk_B_3)),
% 0.80/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.01  thf('157', plain,
% 0.80/1.01      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.80/1.01        | ~ (v2_struct_0 @ sk_B_3))),
% 0.80/1.01      inference('demod', [status(thm)], ['155', '156'])).
% 0.80/1.01  thf('158', plain, ((v2_struct_0 @ sk_B_3)),
% 0.80/1.01      inference('sup-', [status(thm)], ['36', '51'])).
% 0.80/1.01  thf('159', plain,
% 0.80/1.01      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 0.80/1.01      inference('demod', [status(thm)], ['157', '158'])).
% 0.80/1.01  thf('160', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['20', '52'])).
% 0.80/1.01  thf('161', plain,
% 0.80/1.01      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 0.80/1.01      inference('demod', [status(thm)], ['159', '160'])).
% 0.80/1.01  thf('162', plain, ((v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 0.80/1.01      inference('demod', [status(thm)], ['139', '152', '161'])).
% 0.80/1.01  thf('163', plain, ($false), inference('demod', [status(thm)], ['54', '162'])).
% 0.80/1.01  
% 0.80/1.01  % SZS output end Refutation
% 0.80/1.01  
% 0.80/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
