%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PydClwHhCm

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:44 EST 2020

% Result     : Theorem 5.02s
% Output     : Refutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  268 (3460 expanded)
%              Number of leaves         :   72 (1091 expanded)
%              Depth                    :   21
%              Number of atoms          : 1838 (50197 expanded)
%              Number of equality atoms :   90 ( 852 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

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
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_3 ) ),
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
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( ( k2_struct_0 @ X47 )
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
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X44: $i] :
      ( ( l1_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X44: $i] :
      ( ( l1_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('30',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_3 @ X0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
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

thf('34',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( l1_pre_topc @ X58 )
      | ~ ( zip_tseitin_0 @ X58 @ X59 )
      | ( zip_tseitin_2 @ X60 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X59 ) @ ( u1_struct_0 @ X58 ) ) ) )
      | ~ ( v1_funct_2 @ X60 @ ( u1_struct_0 @ X59 ) @ ( u1_struct_0 @ X58 ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('45',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v1_tdlat_3 @ X71 )
      | ( v3_pre_topc @ X72 @ X71 )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X71 ) ) )
      | ~ ( l1_pre_topc @ X71 )
      | ~ ( v2_pre_topc @ X71 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X49: $i,X50: $i,X52: $i,X53: $i] :
      ( ( zip_tseitin_1 @ X49 @ X52 @ X50 @ X53 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X53 ) @ ( u1_struct_0 @ X50 ) @ X52 @ X49 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X54 @ X55 @ X56 ) @ X56 @ X55 @ X54 )
      | ( v5_pre_topc @ X56 @ X54 @ X55 )
      | ~ ( zip_tseitin_2 @ X56 @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('58',plain,(
    ~ ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ) ),
    inference(demod,[status(thm)],['0','57'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('59',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
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

thf('61',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v2_pre_topc @ X61 )
      | ~ ( l1_pre_topc @ X61 )
      | ( m1_subset_1 @ ( sk_D_1 @ X62 @ X61 @ X63 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( v5_pre_topc @ X62 @ X63 @ X61 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X63 ) @ ( u1_struct_0 @ X61 ) ) ) )
      | ~ ( v1_funct_2 @ X62 @ ( u1_struct_0 @ X63 ) @ ( u1_struct_0 @ X61 ) )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( l1_pre_topc @ X63 )
      | ~ ( v2_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('62',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_3 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_pre_topc @ sk_B_3 )
    | ~ ( v2_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_3 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','67','68'])).

thf('70',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( ( k2_struct_0 @ X47 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ sk_B_3 ) @ X0 )
      | ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_3 ) @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_3 ) @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( ( u1_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('89',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_3 ) @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A )
    | ( ( u1_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('93',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('95',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B_3 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B_3 ) @ ( k2_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('98',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A )
    | ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('100',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['98','101'])).

thf('103',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('104',plain,
    ( ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('106',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('107',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('110',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','108','109'])).

thf('111',plain,(
    v1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','110'])).

thf('112',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('113',plain,
    ( ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v2_pre_topc @ X61 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X63 @ ( k8_relset_1 @ ( u1_struct_0 @ X63 ) @ ( u1_struct_0 @ X61 ) @ X62 @ ( sk_D_1 @ X62 @ X61 @ X63 ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X63 ) @ ( u1_struct_0 @ X61 ) @ X62 @ ( k2_pre_topc @ X61 @ ( sk_D_1 @ X62 @ X61 @ X63 ) ) ) )
      | ( v5_pre_topc @ X62 @ X63 @ X61 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X63 ) @ ( u1_struct_0 @ X61 ) ) ) )
      | ~ ( v1_funct_2 @ X62 @ ( u1_struct_0 @ X63 ) @ ( u1_struct_0 @ X61 ) )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( l1_pre_topc @ X63 )
      | ~ ( v2_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('115',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ k1_xboole_0 @ ( k2_pre_topc @ sk_B_3 @ k1_xboole_0 ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) )
    | ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 )
    | ~ ( l1_pre_topc @ sk_B_3 )
    | ~ ( v2_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('117',plain,
    ( ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('118',plain,(
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

thf('119',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k8_relset_1 @ X38 @ X39 @ X40 @ X39 )
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('122',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A )
      & ( v8_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v4_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ) )).

thf('125',plain,(
    ! [X69: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X69 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf('126',plain,(
    m1_subset_1 @ ( k1_yellow_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    r1_tarski @ ( k1_yellow_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('130',plain,
    ( ( k1_yellow_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X68: $i] :
      ( v1_partfun1 @ ( k1_yellow_1 @ X68 ) @ X68 ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf('132',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['130','131'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('133',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_partfun1 @ X42 @ X41 )
      | ( ( k1_relat_1 @ X42 )
        = X41 )
      | ~ ( v4_relat_1 @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('136',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('137',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('139',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('140',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['134','137','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['120','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('146',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('148',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v1_tdlat_3 @ X73 )
      | ( v4_pre_topc @ X74 @ X73 )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X73 ) ) )
      | ~ ( l1_pre_topc @ X73 )
      | ~ ( v2_pre_topc @ X73 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','149'])).

thf('151',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

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

thf('155',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v4_pre_topc @ X45 @ X46 )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = X45 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('162',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v2_pre_topc @ X46 )
      | ( ( k2_pre_topc @ X46 @ X45 )
       != X45 )
      | ( v4_pre_topc @ X45 @ X46 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('171',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('174',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('176',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('181',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('183',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('185',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('187',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('189',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('190',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('191',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ),
    inference(demod,[status(thm)],['115','116','117','143','174','175','176','177','178','181','182','187','188','189','190','191','192'])).

thf('194',plain,(
    $false ),
    inference(demod,[status(thm)],['58','193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PydClwHhCm
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:31:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 5.02/5.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.02/5.20  % Solved by: fo/fo7.sh
% 5.02/5.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.02/5.20  % done 6790 iterations in 4.698s
% 5.02/5.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.02/5.20  % SZS output start Refutation
% 5.02/5.20  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.02/5.20  thf(sk_B_3_type, type, sk_B_3: $i).
% 5.02/5.20  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.02/5.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.02/5.20  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 5.02/5.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.02/5.20  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 5.02/5.20  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.02/5.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.02/5.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.02/5.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.02/5.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.02/5.20  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.02/5.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.02/5.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.02/5.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.02/5.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.02/5.20  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 5.02/5.20  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 5.02/5.20  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 5.02/5.20  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.02/5.20  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 5.02/5.20  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.02/5.20  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.02/5.20  thf(sk_B_type, type, sk_B: $i > $i).
% 5.02/5.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.02/5.20  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 5.02/5.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.02/5.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.02/5.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.02/5.20  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.02/5.20  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 5.02/5.20  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.02/5.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.02/5.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.02/5.20  thf(sk_C_type, type, sk_C: $i).
% 5.02/5.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.02/5.20  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 5.02/5.20  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 5.02/5.20  thf(sk_A_type, type, sk_A: $i).
% 5.02/5.20  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 5.02/5.20  thf(t68_tex_2, conjecture,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.02/5.20       ( ![B:$i]:
% 5.02/5.20         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 5.02/5.20           ( ![C:$i]:
% 5.02/5.20             ( ( ( v1_funct_1 @ C ) & 
% 5.02/5.20                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.02/5.20                 ( m1_subset_1 @
% 5.02/5.20                   C @ 
% 5.02/5.20                   ( k1_zfmisc_1 @
% 5.02/5.20                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.02/5.20               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 5.02/5.20  thf(zf_stmt_0, negated_conjecture,
% 5.02/5.20    (~( ![A:$i]:
% 5.02/5.20        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.02/5.20          ( ![B:$i]:
% 5.02/5.20            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 5.02/5.20              ( ![C:$i]:
% 5.02/5.20                ( ( ( v1_funct_1 @ C ) & 
% 5.02/5.20                    ( v1_funct_2 @
% 5.02/5.20                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.02/5.20                    ( m1_subset_1 @
% 5.02/5.20                      C @ 
% 5.02/5.20                      ( k1_zfmisc_1 @
% 5.02/5.20                        ( k2_zfmisc_1 @
% 5.02/5.20                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.02/5.20                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 5.02/5.20    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 5.02/5.20  thf('0', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf(t55_tops_2, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( l1_pre_topc @ A ) =>
% 5.02/5.20       ( ![B:$i]:
% 5.02/5.20         ( ( l1_pre_topc @ B ) =>
% 5.02/5.20           ( ![C:$i]:
% 5.02/5.20             ( ( ( m1_subset_1 @
% 5.02/5.20                   C @ 
% 5.02/5.20                   ( k1_zfmisc_1 @
% 5.02/5.20                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 5.02/5.20                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.02/5.20                 ( v1_funct_1 @ C ) ) =>
% 5.02/5.20               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 5.02/5.20                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 5.02/5.20                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 5.02/5.20                   ( ![D:$i]:
% 5.02/5.20                     ( ( m1_subset_1 @
% 5.02/5.20                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 5.02/5.20                       ( ( v3_pre_topc @ D @ B ) =>
% 5.02/5.20                         ( v3_pre_topc @
% 5.02/5.20                           ( k8_relset_1 @
% 5.02/5.20                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 5.02/5.20                           A ) ) ) ) ) ) ) ) ) ) ))).
% 5.02/5.20  thf(zf_stmt_1, axiom,
% 5.02/5.20    (![B:$i,A:$i]:
% 5.02/5.20     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 5.02/5.20         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 5.02/5.20       ( zip_tseitin_0 @ B @ A ) ))).
% 5.02/5.20  thf('1', plain,
% 5.02/5.20      (![X47 : $i, X48 : $i]:
% 5.02/5.20         ((zip_tseitin_0 @ X47 @ X48) | ((k2_struct_0 @ X47) = (k1_xboole_0)))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.02/5.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.02/5.20  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.02/5.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.02/5.20  thf('3', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 5.02/5.20      inference('sup+', [status(thm)], ['1', '2'])).
% 5.02/5.20  thf(d3_struct_0, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.02/5.20  thf('4', plain,
% 5.02/5.20      (![X43 : $i]:
% 5.02/5.20         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 5.02/5.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.02/5.20  thf(l13_xboole_0, axiom,
% 5.02/5.20    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 5.02/5.20  thf('5', plain,
% 5.02/5.20      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 5.02/5.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.02/5.20  thf(t113_zfmisc_1, axiom,
% 5.02/5.20    (![A:$i,B:$i]:
% 5.02/5.20     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.02/5.20       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.02/5.20  thf('6', plain,
% 5.02/5.20      (![X11 : $i, X12 : $i]:
% 5.02/5.20         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 5.02/5.20          | ((X12) != (k1_xboole_0)))),
% 5.02/5.20      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.02/5.20  thf('7', plain,
% 5.02/5.20      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 5.02/5.20      inference('simplify', [status(thm)], ['6'])).
% 5.02/5.20  thf('8', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.02/5.20      inference('sup+', [status(thm)], ['5', '7'])).
% 5.02/5.20  thf('9', plain,
% 5.02/5.20      (![X43 : $i]:
% 5.02/5.20         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 5.02/5.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.02/5.20  thf('10', plain,
% 5.02/5.20      ((m1_subset_1 @ sk_C @ 
% 5.02/5.20        (k1_zfmisc_1 @ 
% 5.02/5.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf(t3_subset, axiom,
% 5.02/5.20    (![A:$i,B:$i]:
% 5.02/5.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.02/5.20  thf('11', plain,
% 5.02/5.20      (![X16 : $i, X17 : $i]:
% 5.02/5.20         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 5.02/5.20      inference('cnf', [status(esa)], [t3_subset])).
% 5.02/5.20  thf('12', plain,
% 5.02/5.20      ((r1_tarski @ sk_C @ 
% 5.02/5.20        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['10', '11'])).
% 5.02/5.20  thf('13', plain,
% 5.02/5.20      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 5.02/5.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.02/5.20  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.02/5.20  thf('14', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 5.02/5.20      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.02/5.20  thf(d10_xboole_0, axiom,
% 5.02/5.20    (![A:$i,B:$i]:
% 5.02/5.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.02/5.20  thf('15', plain,
% 5.02/5.20      (![X4 : $i, X6 : $i]:
% 5.02/5.20         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 5.02/5.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.02/5.20  thf('16', plain,
% 5.02/5.20      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['14', '15'])).
% 5.02/5.20  thf('17', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         (~ (r1_tarski @ X1 @ X0)
% 5.02/5.20          | ~ (v1_xboole_0 @ X0)
% 5.02/5.20          | ((X1) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['13', '16'])).
% 5.02/5.20  thf('18', plain,
% 5.02/5.20      ((((sk_C) = (k1_xboole_0))
% 5.02/5.20        | ~ (v1_xboole_0 @ 
% 5.02/5.20             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 5.02/5.20      inference('sup-', [status(thm)], ['12', '17'])).
% 5.02/5.20  thf('19', plain,
% 5.02/5.20      ((~ (v1_xboole_0 @ 
% 5.02/5.20           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))
% 5.02/5.20        | ~ (l1_struct_0 @ sk_A)
% 5.02/5.20        | ((sk_C) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['9', '18'])).
% 5.02/5.20  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf(dt_l1_pre_topc, axiom,
% 5.02/5.20    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.02/5.20  thf('21', plain,
% 5.02/5.20      (![X44 : $i]: ((l1_struct_0 @ X44) | ~ (l1_pre_topc @ X44))),
% 5.02/5.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.02/5.20  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 5.02/5.20      inference('sup-', [status(thm)], ['20', '21'])).
% 5.02/5.20  thf('23', plain,
% 5.02/5.20      ((~ (v1_xboole_0 @ 
% 5.02/5.20           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))
% 5.02/5.20        | ((sk_C) = (k1_xboole_0)))),
% 5.02/5.20      inference('demod', [status(thm)], ['19', '22'])).
% 5.02/5.20  thf('24', plain,
% 5.02/5.20      ((~ (v1_xboole_0 @ k1_xboole_0)
% 5.02/5.20        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 5.02/5.20        | ((sk_C) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['8', '23'])).
% 5.02/5.20  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.02/5.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.02/5.20  thf('26', plain,
% 5.02/5.20      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3)) | ((sk_C) = (k1_xboole_0)))),
% 5.02/5.20      inference('demod', [status(thm)], ['24', '25'])).
% 5.02/5.20  thf('27', plain,
% 5.02/5.20      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 5.02/5.20        | ~ (l1_struct_0 @ sk_B_3)
% 5.02/5.20        | ((sk_C) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['4', '26'])).
% 5.02/5.20  thf('28', plain, ((l1_pre_topc @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('29', plain,
% 5.02/5.20      (![X44 : $i]: ((l1_struct_0 @ X44) | ~ (l1_pre_topc @ X44))),
% 5.02/5.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.02/5.20  thf('30', plain, ((l1_struct_0 @ sk_B_3)),
% 5.02/5.20      inference('sup-', [status(thm)], ['28', '29'])).
% 5.02/5.20  thf('31', plain,
% 5.02/5.20      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3)) | ((sk_C) = (k1_xboole_0)))),
% 5.02/5.20      inference('demod', [status(thm)], ['27', '30'])).
% 5.02/5.20  thf('32', plain,
% 5.02/5.20      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_3 @ X0) | ((sk_C) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['3', '31'])).
% 5.02/5.20  thf('33', plain,
% 5.02/5.20      ((m1_subset_1 @ sk_C @ 
% 5.02/5.20        (k1_zfmisc_1 @ 
% 5.02/5.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 5.02/5.20  thf(zf_stmt_3, axiom,
% 5.02/5.20    (![C:$i,B:$i,A:$i]:
% 5.02/5.20     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 5.02/5.20       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 5.02/5.20         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 5.02/5.20  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 5.02/5.20  thf(zf_stmt_5, axiom,
% 5.02/5.20    (![D:$i,C:$i,B:$i,A:$i]:
% 5.02/5.20     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 5.02/5.20       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 5.02/5.20         ( ( v3_pre_topc @ D @ B ) =>
% 5.02/5.20           ( v3_pre_topc @
% 5.02/5.20             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 5.02/5.20             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 5.02/5.20  thf(zf_stmt_7, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( l1_pre_topc @ A ) =>
% 5.02/5.20       ( ![B:$i]:
% 5.02/5.20         ( ( l1_pre_topc @ B ) =>
% 5.02/5.20           ( ![C:$i]:
% 5.02/5.20             ( ( ( v1_funct_1 @ C ) & 
% 5.02/5.20                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.02/5.20                 ( m1_subset_1 @
% 5.02/5.20                   C @ 
% 5.02/5.20                   ( k1_zfmisc_1 @
% 5.02/5.20                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.02/5.20               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 5.02/5.20  thf('34', plain,
% 5.02/5.20      (![X58 : $i, X59 : $i, X60 : $i]:
% 5.02/5.20         (~ (l1_pre_topc @ X58)
% 5.02/5.20          | ~ (zip_tseitin_0 @ X58 @ X59)
% 5.02/5.20          | (zip_tseitin_2 @ X60 @ X58 @ X59)
% 5.02/5.20          | ~ (m1_subset_1 @ X60 @ 
% 5.02/5.20               (k1_zfmisc_1 @ 
% 5.02/5.20                (k2_zfmisc_1 @ (u1_struct_0 @ X59) @ (u1_struct_0 @ X58))))
% 5.02/5.20          | ~ (v1_funct_2 @ X60 @ (u1_struct_0 @ X59) @ (u1_struct_0 @ X58))
% 5.02/5.20          | ~ (v1_funct_1 @ X60)
% 5.02/5.20          | ~ (l1_pre_topc @ X59))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_7])).
% 5.02/5.20  thf('35', plain,
% 5.02/5.20      ((~ (l1_pre_topc @ sk_A)
% 5.02/5.20        | ~ (v1_funct_1 @ sk_C)
% 5.02/5.20        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))
% 5.02/5.20        | (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)
% 5.02/5.20        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A)
% 5.02/5.20        | ~ (l1_pre_topc @ sk_B_3))),
% 5.02/5.20      inference('sup-', [status(thm)], ['33', '34'])).
% 5.02/5.20  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('38', plain,
% 5.02/5.20      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('39', plain, ((l1_pre_topc @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('40', plain,
% 5.02/5.20      (((zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)
% 5.02/5.20        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 5.02/5.20  thf('41', plain,
% 5.02/5.20      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('sup-', [status(thm)], ['32', '40'])).
% 5.02/5.20  thf('42', plain,
% 5.02/5.20      ((m1_subset_1 @ sk_C @ 
% 5.02/5.20        (k1_zfmisc_1 @ 
% 5.02/5.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf(dt_k8_relset_1, axiom,
% 5.02/5.20    (![A:$i,B:$i,C:$i,D:$i]:
% 5.02/5.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.02/5.20       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.02/5.20  thf('43', plain,
% 5.02/5.20      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 5.02/5.20         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 5.02/5.20          | (m1_subset_1 @ (k8_relset_1 @ X32 @ X33 @ X31 @ X34) @ 
% 5.02/5.20             (k1_zfmisc_1 @ X32)))),
% 5.02/5.20      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 5.02/5.20  thf('44', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (m1_subset_1 @ 
% 5.02/5.20          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 5.02/5.20           sk_C @ X0) @ 
% 5.02/5.20          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['42', '43'])).
% 5.02/5.20  thf(t17_tdlat_3, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.02/5.20       ( ( v1_tdlat_3 @ A ) <=>
% 5.02/5.20         ( ![B:$i]:
% 5.02/5.20           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.02/5.20             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 5.02/5.20  thf('45', plain,
% 5.02/5.20      (![X71 : $i, X72 : $i]:
% 5.02/5.20         (~ (v1_tdlat_3 @ X71)
% 5.02/5.20          | (v3_pre_topc @ X72 @ X71)
% 5.02/5.20          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (u1_struct_0 @ X71)))
% 5.02/5.20          | ~ (l1_pre_topc @ X71)
% 5.02/5.20          | ~ (v2_pre_topc @ X71))),
% 5.02/5.20      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 5.02/5.20  thf('46', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (~ (v2_pre_topc @ sk_A)
% 5.02/5.20          | ~ (l1_pre_topc @ sk_A)
% 5.02/5.20          | (v3_pre_topc @ 
% 5.02/5.20             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 5.02/5.20              sk_C @ X0) @ 
% 5.02/5.20             sk_A)
% 5.02/5.20          | ~ (v1_tdlat_3 @ sk_A))),
% 5.02/5.20      inference('sup-', [status(thm)], ['44', '45'])).
% 5.02/5.20  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('49', plain, ((v1_tdlat_3 @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('50', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (v3_pre_topc @ 
% 5.02/5.20          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 5.02/5.20           sk_C @ X0) @ 
% 5.02/5.20          sk_A)),
% 5.02/5.20      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 5.02/5.20  thf('51', plain,
% 5.02/5.20      (![X49 : $i, X50 : $i, X52 : $i, X53 : $i]:
% 5.02/5.20         ((zip_tseitin_1 @ X49 @ X52 @ X50 @ X53)
% 5.02/5.20          | ~ (v3_pre_topc @ 
% 5.02/5.20               (k8_relset_1 @ (u1_struct_0 @ X53) @ (u1_struct_0 @ X50) @ 
% 5.02/5.20                X52 @ X49) @ 
% 5.02/5.20               X53))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.02/5.20  thf('52', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_C @ sk_B_3 @ sk_A)),
% 5.02/5.20      inference('sup-', [status(thm)], ['50', '51'])).
% 5.02/5.20  thf('53', plain,
% 5.02/5.20      (![X54 : $i, X55 : $i, X56 : $i]:
% 5.02/5.20         (~ (zip_tseitin_1 @ (sk_D @ X54 @ X55 @ X56) @ X56 @ X55 @ X54)
% 5.02/5.20          | (v5_pre_topc @ X56 @ X54 @ X55)
% 5.02/5.20          | ~ (zip_tseitin_2 @ X56 @ X55 @ X54))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.02/5.20  thf('54', plain,
% 5.02/5.20      ((~ (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)
% 5.02/5.20        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_3))),
% 5.02/5.20      inference('sup-', [status(thm)], ['52', '53'])).
% 5.02/5.20  thf('55', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('56', plain, (~ (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)),
% 5.02/5.20      inference('clc', [status(thm)], ['54', '55'])).
% 5.02/5.20  thf('57', plain, (((sk_C) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['41', '56'])).
% 5.02/5.20  thf('58', plain, (~ (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 5.02/5.20      inference('demod', [status(thm)], ['0', '57'])).
% 5.02/5.20  thf(d1_xboole_0, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.02/5.20  thf('59', plain,
% 5.02/5.20      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 5.02/5.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.02/5.20  thf('60', plain,
% 5.02/5.20      ((m1_subset_1 @ sk_C @ 
% 5.02/5.20        (k1_zfmisc_1 @ 
% 5.02/5.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf(t56_tops_2, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.02/5.20       ( ![B:$i]:
% 5.02/5.20         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 5.02/5.20           ( ![C:$i]:
% 5.02/5.20             ( ( ( v1_funct_1 @ C ) & 
% 5.02/5.20                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.02/5.20                 ( m1_subset_1 @
% 5.02/5.20                   C @ 
% 5.02/5.20                   ( k1_zfmisc_1 @
% 5.02/5.20                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.02/5.20               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 5.02/5.20                 ( ![D:$i]:
% 5.02/5.20                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 5.02/5.20                     ( r1_tarski @
% 5.02/5.20                       ( k2_pre_topc @
% 5.02/5.20                         A @ 
% 5.02/5.20                         ( k8_relset_1 @
% 5.02/5.20                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 5.02/5.20                       ( k8_relset_1 @
% 5.02/5.20                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 5.02/5.20                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 5.02/5.20  thf('61', plain,
% 5.02/5.20      (![X61 : $i, X62 : $i, X63 : $i]:
% 5.02/5.20         (~ (v2_pre_topc @ X61)
% 5.02/5.20          | ~ (l1_pre_topc @ X61)
% 5.02/5.20          | (m1_subset_1 @ (sk_D_1 @ X62 @ X61 @ X63) @ 
% 5.02/5.20             (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 5.02/5.20          | (v5_pre_topc @ X62 @ X63 @ X61)
% 5.02/5.20          | ~ (m1_subset_1 @ X62 @ 
% 5.02/5.20               (k1_zfmisc_1 @ 
% 5.02/5.20                (k2_zfmisc_1 @ (u1_struct_0 @ X63) @ (u1_struct_0 @ X61))))
% 5.02/5.20          | ~ (v1_funct_2 @ X62 @ (u1_struct_0 @ X63) @ (u1_struct_0 @ X61))
% 5.02/5.20          | ~ (v1_funct_1 @ X62)
% 5.02/5.20          | ~ (l1_pre_topc @ X63)
% 5.02/5.20          | ~ (v2_pre_topc @ X63))),
% 5.02/5.20      inference('cnf', [status(esa)], [t56_tops_2])).
% 5.02/5.20  thf('62', plain,
% 5.02/5.20      ((~ (v2_pre_topc @ sk_A)
% 5.02/5.20        | ~ (l1_pre_topc @ sk_A)
% 5.02/5.20        | ~ (v1_funct_1 @ sk_C)
% 5.02/5.20        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))
% 5.02/5.20        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_3)
% 5.02/5.20        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A) @ 
% 5.02/5.20           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))
% 5.02/5.20        | ~ (l1_pre_topc @ sk_B_3)
% 5.02/5.20        | ~ (v2_pre_topc @ sk_B_3))),
% 5.02/5.20      inference('sup-', [status(thm)], ['60', '61'])).
% 5.02/5.20  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('66', plain,
% 5.02/5.20      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('67', plain, ((l1_pre_topc @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('68', plain, ((v2_pre_topc @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('69', plain,
% 5.02/5.20      (((v5_pre_topc @ sk_C @ sk_A @ sk_B_3)
% 5.02/5.20        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A) @ 
% 5.02/5.20           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3))))),
% 5.02/5.20      inference('demod', [status(thm)],
% 5.02/5.20                ['62', '63', '64', '65', '66', '67', '68'])).
% 5.02/5.20  thf('70', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('71', plain,
% 5.02/5.20      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A) @ 
% 5.02/5.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 5.02/5.20      inference('clc', [status(thm)], ['69', '70'])).
% 5.02/5.20  thf(t5_subset, axiom,
% 5.02/5.20    (![A:$i,B:$i,C:$i]:
% 5.02/5.20     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 5.02/5.20          ( v1_xboole_0 @ C ) ) ))).
% 5.02/5.20  thf('72', plain,
% 5.02/5.20      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.02/5.20         (~ (r2_hidden @ X22 @ X23)
% 5.02/5.20          | ~ (v1_xboole_0 @ X24)
% 5.02/5.20          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 5.02/5.20      inference('cnf', [status(esa)], [t5_subset])).
% 5.02/5.20  thf('73', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 5.02/5.20          | ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['71', '72'])).
% 5.02/5.20  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['41', '56'])).
% 5.02/5.20  thf('75', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 5.02/5.20          | ~ (r2_hidden @ X0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A)))),
% 5.02/5.20      inference('demod', [status(thm)], ['73', '74'])).
% 5.02/5.20  thf('76', plain,
% 5.02/5.20      (![X47 : $i, X48 : $i]:
% 5.02/5.20         ((zip_tseitin_0 @ X47 @ X48) | ((k2_struct_0 @ X47) = (k1_xboole_0)))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.02/5.20  thf('77', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 5.02/5.20      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.02/5.20  thf('78', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.02/5.20         ((r1_tarski @ (k2_struct_0 @ X0) @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 5.02/5.20      inference('sup+', [status(thm)], ['76', '77'])).
% 5.02/5.20  thf('79', plain,
% 5.02/5.20      (((zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)
% 5.02/5.20        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 5.02/5.20  thf('80', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         ((r1_tarski @ (k2_struct_0 @ sk_B_3) @ X0)
% 5.02/5.20          | (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('sup-', [status(thm)], ['78', '79'])).
% 5.02/5.20  thf('81', plain,
% 5.02/5.20      (![X43 : $i]:
% 5.02/5.20         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 5.02/5.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.02/5.20  thf('82', plain,
% 5.02/5.20      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A) @ 
% 5.02/5.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 5.02/5.20      inference('clc', [status(thm)], ['69', '70'])).
% 5.02/5.20  thf('83', plain,
% 5.02/5.20      (![X16 : $i, X17 : $i]:
% 5.02/5.20         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 5.02/5.20      inference('cnf', [status(esa)], [t3_subset])).
% 5.02/5.20  thf('84', plain,
% 5.02/5.20      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 5.02/5.20      inference('sup-', [status(thm)], ['82', '83'])).
% 5.02/5.20  thf('85', plain,
% 5.02/5.20      (![X4 : $i, X6 : $i]:
% 5.02/5.20         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 5.02/5.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.02/5.20  thf('86', plain,
% 5.02/5.20      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_3) @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A))
% 5.02/5.20        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C @ sk_B_3 @ sk_A)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['84', '85'])).
% 5.02/5.20  thf('87', plain,
% 5.02/5.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_3) @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A))
% 5.02/5.20        | ~ (l1_struct_0 @ sk_B_3)
% 5.02/5.20        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C @ sk_B_3 @ sk_A)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['81', '86'])).
% 5.02/5.20  thf('88', plain, ((l1_struct_0 @ sk_B_3)),
% 5.02/5.20      inference('sup-', [status(thm)], ['28', '29'])).
% 5.02/5.20  thf('89', plain,
% 5.02/5.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_3) @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A))
% 5.02/5.20        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C @ sk_B_3 @ sk_A)))),
% 5.02/5.20      inference('demod', [status(thm)], ['87', '88'])).
% 5.02/5.20  thf('90', plain,
% 5.02/5.20      (((zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)
% 5.02/5.20        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C @ sk_B_3 @ sk_A)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['80', '89'])).
% 5.02/5.20  thf('91', plain,
% 5.02/5.20      (![X43 : $i]:
% 5.02/5.20         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 5.02/5.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.02/5.20  thf('92', plain,
% 5.02/5.20      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 5.02/5.20      inference('sup-', [status(thm)], ['82', '83'])).
% 5.02/5.20  thf('93', plain,
% 5.02/5.20      (((r1_tarski @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A) @ (k2_struct_0 @ sk_B_3))
% 5.02/5.20        | ~ (l1_struct_0 @ sk_B_3))),
% 5.02/5.20      inference('sup+', [status(thm)], ['91', '92'])).
% 5.02/5.20  thf('94', plain, ((l1_struct_0 @ sk_B_3)),
% 5.02/5.20      inference('sup-', [status(thm)], ['28', '29'])).
% 5.02/5.20  thf('95', plain,
% 5.02/5.20      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B_3 @ sk_A) @ (k2_struct_0 @ sk_B_3))),
% 5.02/5.20      inference('demod', [status(thm)], ['93', '94'])).
% 5.02/5.20  thf('96', plain,
% 5.02/5.20      (((r1_tarski @ (u1_struct_0 @ sk_B_3) @ (k2_struct_0 @ sk_B_3))
% 5.02/5.20        | (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('sup+', [status(thm)], ['90', '95'])).
% 5.02/5.20  thf('97', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         (~ (r1_tarski @ X1 @ X0)
% 5.02/5.20          | ~ (v1_xboole_0 @ X0)
% 5.02/5.20          | ((X1) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['13', '16'])).
% 5.02/5.20  thf('98', plain,
% 5.02/5.20      (((zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)
% 5.02/5.20        | ((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 5.02/5.20        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['96', '97'])).
% 5.02/5.20  thf('99', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 5.02/5.20      inference('sup+', [status(thm)], ['1', '2'])).
% 5.02/5.20  thf('100', plain,
% 5.02/5.20      (((zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)
% 5.02/5.20        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 5.02/5.20  thf('101', plain,
% 5.02/5.20      (((v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 5.02/5.20        | (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('sup-', [status(thm)], ['99', '100'])).
% 5.02/5.20  thf('102', plain,
% 5.02/5.20      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 5.02/5.20        | (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('clc', [status(thm)], ['98', '101'])).
% 5.02/5.20  thf('103', plain, (((sk_C) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['41', '56'])).
% 5.02/5.20  thf('104', plain,
% 5.02/5.20      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 5.02/5.20        | (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('demod', [status(thm)], ['102', '103'])).
% 5.02/5.20  thf('105', plain, (~ (zip_tseitin_2 @ sk_C @ sk_B_3 @ sk_A)),
% 5.02/5.20      inference('clc', [status(thm)], ['54', '55'])).
% 5.02/5.20  thf('106', plain, (((sk_C) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['41', '56'])).
% 5.02/5.20  thf('107', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)),
% 5.02/5.20      inference('demod', [status(thm)], ['105', '106'])).
% 5.02/5.20  thf('108', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 5.02/5.20      inference('clc', [status(thm)], ['104', '107'])).
% 5.02/5.20  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.02/5.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.02/5.20  thf('110', plain,
% 5.02/5.20      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('demod', [status(thm)], ['75', '108', '109'])).
% 5.02/5.20  thf('111', plain, ((v1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 5.02/5.20      inference('sup-', [status(thm)], ['59', '110'])).
% 5.02/5.20  thf('112', plain,
% 5.02/5.20      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 5.02/5.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.02/5.20  thf('113', plain, (((sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['111', '112'])).
% 5.02/5.20  thf('114', plain,
% 5.02/5.20      (![X61 : $i, X62 : $i, X63 : $i]:
% 5.02/5.20         (~ (v2_pre_topc @ X61)
% 5.02/5.20          | ~ (l1_pre_topc @ X61)
% 5.02/5.20          | ~ (r1_tarski @ 
% 5.02/5.20               (k2_pre_topc @ X63 @ 
% 5.02/5.20                (k8_relset_1 @ (u1_struct_0 @ X63) @ (u1_struct_0 @ X61) @ 
% 5.02/5.20                 X62 @ (sk_D_1 @ X62 @ X61 @ X63))) @ 
% 5.02/5.20               (k8_relset_1 @ (u1_struct_0 @ X63) @ (u1_struct_0 @ X61) @ 
% 5.02/5.20                X62 @ (k2_pre_topc @ X61 @ (sk_D_1 @ X62 @ X61 @ X63))))
% 5.02/5.20          | (v5_pre_topc @ X62 @ X63 @ X61)
% 5.02/5.20          | ~ (m1_subset_1 @ X62 @ 
% 5.02/5.20               (k1_zfmisc_1 @ 
% 5.02/5.20                (k2_zfmisc_1 @ (u1_struct_0 @ X63) @ (u1_struct_0 @ X61))))
% 5.02/5.20          | ~ (v1_funct_2 @ X62 @ (u1_struct_0 @ X63) @ (u1_struct_0 @ X61))
% 5.02/5.20          | ~ (v1_funct_1 @ X62)
% 5.02/5.20          | ~ (l1_pre_topc @ X63)
% 5.02/5.20          | ~ (v2_pre_topc @ X63))),
% 5.02/5.20      inference('cnf', [status(esa)], [t56_tops_2])).
% 5.02/5.20  thf('115', plain,
% 5.02/5.20      ((~ (r1_tarski @ 
% 5.02/5.20           (k2_pre_topc @ sk_A @ 
% 5.02/5.20            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 5.02/5.20             k1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))) @ 
% 5.02/5.20           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 5.02/5.20            k1_xboole_0 @ (k2_pre_topc @ sk_B_3 @ k1_xboole_0)))
% 5.02/5.20        | ~ (v2_pre_topc @ sk_A)
% 5.02/5.20        | ~ (l1_pre_topc @ sk_A)
% 5.02/5.20        | ~ (v1_funct_1 @ k1_xboole_0)
% 5.02/5.20        | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.02/5.20             (u1_struct_0 @ sk_B_3))
% 5.02/5.20        | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 5.02/5.20             (k1_zfmisc_1 @ 
% 5.02/5.20              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))
% 5.02/5.20        | (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)
% 5.02/5.20        | ~ (l1_pre_topc @ sk_B_3)
% 5.02/5.20        | ~ (v2_pre_topc @ sk_B_3))),
% 5.02/5.20      inference('sup-', [status(thm)], ['113', '114'])).
% 5.02/5.20  thf('116', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 5.02/5.20      inference('clc', [status(thm)], ['104', '107'])).
% 5.02/5.20  thf('117', plain, (((sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['111', '112'])).
% 5.02/5.20  thf(t4_subset_1, axiom,
% 5.02/5.20    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.02/5.20  thf('118', plain,
% 5.02/5.20      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 5.02/5.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.02/5.20  thf(t38_relset_1, axiom,
% 5.02/5.20    (![A:$i,B:$i,C:$i]:
% 5.02/5.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.02/5.20       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 5.02/5.20         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.02/5.20  thf('119', plain,
% 5.02/5.20      (![X38 : $i, X39 : $i, X40 : $i]:
% 5.02/5.20         (((k8_relset_1 @ X38 @ X39 @ X40 @ X39)
% 5.02/5.20            = (k1_relset_1 @ X38 @ X39 @ X40))
% 5.02/5.20          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 5.02/5.20      inference('cnf', [status(esa)], [t38_relset_1])).
% 5.02/5.20  thf('120', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 5.02/5.20           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['118', '119'])).
% 5.02/5.20  thf('121', plain,
% 5.02/5.20      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 5.02/5.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.02/5.20  thf(redefinition_k1_relset_1, axiom,
% 5.02/5.20    (![A:$i,B:$i,C:$i]:
% 5.02/5.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.02/5.20       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.02/5.20  thf('122', plain,
% 5.02/5.20      (![X35 : $i, X36 : $i, X37 : $i]:
% 5.02/5.20         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 5.02/5.20          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 5.02/5.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.02/5.20  thf('123', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['121', '122'])).
% 5.02/5.20  thf('124', plain,
% 5.02/5.20      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 5.02/5.20      inference('simplify', [status(thm)], ['6'])).
% 5.02/5.20  thf(dt_k1_yellow_1, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( m1_subset_1 @
% 5.02/5.20         ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.02/5.20       ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A ) & 
% 5.02/5.20       ( v8_relat_2 @ ( k1_yellow_1 @ A ) ) & 
% 5.02/5.20       ( v4_relat_2 @ ( k1_yellow_1 @ A ) ) & 
% 5.02/5.20       ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ))).
% 5.02/5.20  thf('125', plain,
% 5.02/5.20      (![X69 : $i]:
% 5.02/5.20         (m1_subset_1 @ (k1_yellow_1 @ X69) @ 
% 5.02/5.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X69)))),
% 5.02/5.20      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 5.02/5.20  thf('126', plain,
% 5.02/5.20      ((m1_subset_1 @ (k1_yellow_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 5.02/5.20      inference('sup+', [status(thm)], ['124', '125'])).
% 5.02/5.20  thf('127', plain,
% 5.02/5.20      (![X16 : $i, X17 : $i]:
% 5.02/5.20         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 5.02/5.20      inference('cnf', [status(esa)], [t3_subset])).
% 5.02/5.20  thf('128', plain, ((r1_tarski @ (k1_yellow_1 @ k1_xboole_0) @ k1_xboole_0)),
% 5.02/5.20      inference('sup-', [status(thm)], ['126', '127'])).
% 5.02/5.20  thf('129', plain,
% 5.02/5.20      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['14', '15'])).
% 5.02/5.20  thf('130', plain, (((k1_yellow_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['128', '129'])).
% 5.02/5.20  thf('131', plain, (![X68 : $i]: (v1_partfun1 @ (k1_yellow_1 @ X68) @ X68)),
% 5.02/5.20      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 5.02/5.20  thf('132', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 5.02/5.20      inference('sup+', [status(thm)], ['130', '131'])).
% 5.02/5.20  thf(d4_partfun1, axiom,
% 5.02/5.20    (![A:$i,B:$i]:
% 5.02/5.20     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 5.02/5.20       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 5.02/5.20  thf('133', plain,
% 5.02/5.20      (![X41 : $i, X42 : $i]:
% 5.02/5.20         (~ (v1_partfun1 @ X42 @ X41)
% 5.02/5.20          | ((k1_relat_1 @ X42) = (X41))
% 5.02/5.20          | ~ (v4_relat_1 @ X42 @ X41)
% 5.02/5.20          | ~ (v1_relat_1 @ X42))),
% 5.02/5.20      inference('cnf', [status(esa)], [d4_partfun1])).
% 5.02/5.20  thf('134', plain,
% 5.02/5.20      ((~ (v1_relat_1 @ k1_xboole_0)
% 5.02/5.20        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 5.02/5.20        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 5.02/5.20      inference('sup-', [status(thm)], ['132', '133'])).
% 5.02/5.20  thf('135', plain,
% 5.02/5.20      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 5.02/5.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.02/5.20  thf(cc1_relset_1, axiom,
% 5.02/5.20    (![A:$i,B:$i,C:$i]:
% 5.02/5.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.02/5.20       ( v1_relat_1 @ C ) ))).
% 5.02/5.20  thf('136', plain,
% 5.02/5.20      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.02/5.20         ((v1_relat_1 @ X25)
% 5.02/5.20          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.02/5.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.02/5.20  thf('137', plain, ((v1_relat_1 @ k1_xboole_0)),
% 5.02/5.20      inference('sup-', [status(thm)], ['135', '136'])).
% 5.02/5.20  thf('138', plain,
% 5.02/5.20      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 5.02/5.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.02/5.20  thf(cc2_relset_1, axiom,
% 5.02/5.20    (![A:$i,B:$i,C:$i]:
% 5.02/5.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.02/5.20       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.02/5.20  thf('139', plain,
% 5.02/5.20      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.02/5.20         ((v4_relat_1 @ X28 @ X29)
% 5.02/5.20          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 5.02/5.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.02/5.20  thf('140', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 5.02/5.20      inference('sup-', [status(thm)], ['138', '139'])).
% 5.02/5.20  thf('141', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.02/5.20      inference('demod', [status(thm)], ['134', '137', '140'])).
% 5.02/5.20  thf('142', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.02/5.20      inference('demod', [status(thm)], ['123', '141'])).
% 5.02/5.20  thf('143', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.02/5.20      inference('demod', [status(thm)], ['120', '142'])).
% 5.02/5.20  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('145', plain,
% 5.02/5.20      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 5.02/5.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.02/5.20  thf('146', plain,
% 5.02/5.20      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 5.02/5.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.02/5.20  thf('147', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 5.02/5.20      inference('sup+', [status(thm)], ['145', '146'])).
% 5.02/5.20  thf(t18_tdlat_3, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.02/5.20       ( ( v1_tdlat_3 @ A ) <=>
% 5.02/5.20         ( ![B:$i]:
% 5.02/5.20           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.02/5.20             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 5.02/5.20  thf('148', plain,
% 5.02/5.20      (![X73 : $i, X74 : $i]:
% 5.02/5.20         (~ (v1_tdlat_3 @ X73)
% 5.02/5.20          | (v4_pre_topc @ X74 @ X73)
% 5.02/5.20          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (u1_struct_0 @ X73)))
% 5.02/5.20          | ~ (l1_pre_topc @ X73)
% 5.02/5.20          | ~ (v2_pre_topc @ X73))),
% 5.02/5.20      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 5.02/5.20  thf('149', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         (~ (v1_xboole_0 @ X1)
% 5.02/5.20          | ~ (v2_pre_topc @ X0)
% 5.02/5.20          | ~ (l1_pre_topc @ X0)
% 5.02/5.20          | (v4_pre_topc @ X1 @ X0)
% 5.02/5.20          | ~ (v1_tdlat_3 @ X0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['147', '148'])).
% 5.02/5.20  thf('150', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (~ (v1_tdlat_3 @ sk_A)
% 5.02/5.20          | (v4_pre_topc @ X0 @ sk_A)
% 5.02/5.20          | ~ (v2_pre_topc @ sk_A)
% 5.02/5.20          | ~ (v1_xboole_0 @ X0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['144', '149'])).
% 5.02/5.20  thf('151', plain, ((v1_tdlat_3 @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('153', plain,
% 5.02/5.20      (![X0 : $i]: ((v4_pre_topc @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 5.02/5.20      inference('demod', [status(thm)], ['150', '151', '152'])).
% 5.02/5.20  thf('154', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 5.02/5.20      inference('sup+', [status(thm)], ['145', '146'])).
% 5.02/5.20  thf(t52_pre_topc, axiom,
% 5.02/5.20    (![A:$i]:
% 5.02/5.20     ( ( l1_pre_topc @ A ) =>
% 5.02/5.20       ( ![B:$i]:
% 5.02/5.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.02/5.20           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 5.02/5.20             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 5.02/5.20               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 5.02/5.20  thf('155', plain,
% 5.02/5.20      (![X45 : $i, X46 : $i]:
% 5.02/5.20         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 5.02/5.20          | ~ (v4_pre_topc @ X45 @ X46)
% 5.02/5.20          | ((k2_pre_topc @ X46 @ X45) = (X45))
% 5.02/5.20          | ~ (l1_pre_topc @ X46))),
% 5.02/5.20      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.02/5.20  thf('156', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         (~ (v1_xboole_0 @ X1)
% 5.02/5.20          | ~ (l1_pre_topc @ X0)
% 5.02/5.20          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 5.02/5.20          | ~ (v4_pre_topc @ X1 @ X0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['154', '155'])).
% 5.02/5.20  thf('157', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (~ (v1_xboole_0 @ X0)
% 5.02/5.20          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 5.02/5.20          | ~ (l1_pre_topc @ sk_A)
% 5.02/5.20          | ~ (v1_xboole_0 @ X0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['153', '156'])).
% 5.02/5.20  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('159', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (~ (v1_xboole_0 @ X0)
% 5.02/5.20          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 5.02/5.20          | ~ (v1_xboole_0 @ X0))),
% 5.02/5.20      inference('demod', [status(thm)], ['157', '158'])).
% 5.02/5.20  thf('160', plain,
% 5.02/5.20      (![X0 : $i]: (((k2_pre_topc @ sk_A @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.02/5.20      inference('simplify', [status(thm)], ['159'])).
% 5.02/5.20  thf('161', plain,
% 5.02/5.20      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 5.02/5.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.02/5.20  thf('162', plain,
% 5.02/5.20      (![X45 : $i, X46 : $i]:
% 5.02/5.20         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 5.02/5.20          | ~ (v2_pre_topc @ X46)
% 5.02/5.20          | ((k2_pre_topc @ X46 @ X45) != (X45))
% 5.02/5.20          | (v4_pre_topc @ X45 @ X46)
% 5.02/5.20          | ~ (l1_pre_topc @ X46))),
% 5.02/5.20      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.02/5.20  thf('163', plain,
% 5.02/5.20      (![X0 : $i]:
% 5.02/5.20         (~ (l1_pre_topc @ X0)
% 5.02/5.20          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 5.02/5.20          | ((k2_pre_topc @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 5.02/5.20          | ~ (v2_pre_topc @ X0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['161', '162'])).
% 5.02/5.20  thf('164', plain,
% 5.02/5.20      ((((k1_xboole_0) != (k1_xboole_0))
% 5.02/5.20        | ~ (v1_xboole_0 @ k1_xboole_0)
% 5.02/5.20        | ~ (v2_pre_topc @ sk_A)
% 5.02/5.20        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 5.02/5.20        | ~ (l1_pre_topc @ sk_A))),
% 5.02/5.20      inference('sup-', [status(thm)], ['160', '163'])).
% 5.02/5.20  thf('165', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.02/5.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.02/5.20  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('168', plain,
% 5.02/5.20      ((((k1_xboole_0) != (k1_xboole_0)) | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 5.02/5.20      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 5.02/5.20  thf('169', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 5.02/5.20      inference('simplify', [status(thm)], ['168'])).
% 5.02/5.20  thf('170', plain,
% 5.02/5.20      (![X0 : $i, X1 : $i]:
% 5.02/5.20         (~ (v1_xboole_0 @ X1)
% 5.02/5.20          | ~ (l1_pre_topc @ X0)
% 5.02/5.20          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 5.02/5.20          | ~ (v4_pre_topc @ X1 @ X0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['154', '155'])).
% 5.02/5.20  thf('171', plain,
% 5.02/5.20      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 5.02/5.20        | ~ (l1_pre_topc @ sk_A)
% 5.02/5.20        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['169', '170'])).
% 5.02/5.20  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('173', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.02/5.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.02/5.20  thf('174', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 5.02/5.20      inference('demod', [status(thm)], ['171', '172', '173'])).
% 5.02/5.20  thf('175', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 5.02/5.20      inference('clc', [status(thm)], ['104', '107'])).
% 5.02/5.20  thf('176', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 5.02/5.20      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.02/5.20  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('180', plain, (((sk_C) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['41', '56'])).
% 5.02/5.20  thf('181', plain, ((v1_funct_1 @ k1_xboole_0)),
% 5.02/5.20      inference('demod', [status(thm)], ['179', '180'])).
% 5.02/5.20  thf('182', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 5.02/5.20      inference('clc', [status(thm)], ['104', '107'])).
% 5.02/5.20  thf('183', plain,
% 5.02/5.20      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('184', plain, (((sk_C) = (k1_xboole_0))),
% 5.02/5.20      inference('sup-', [status(thm)], ['41', '56'])).
% 5.02/5.20  thf('185', plain,
% 5.02/5.20      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.02/5.20        (u1_struct_0 @ sk_B_3))),
% 5.02/5.20      inference('demod', [status(thm)], ['183', '184'])).
% 5.02/5.20  thf('186', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 5.02/5.20      inference('clc', [status(thm)], ['104', '107'])).
% 5.02/5.20  thf('187', plain,
% 5.02/5.20      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 5.02/5.20      inference('demod', [status(thm)], ['185', '186'])).
% 5.02/5.20  thf('188', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 5.02/5.20      inference('clc', [status(thm)], ['104', '107'])).
% 5.02/5.20  thf('189', plain,
% 5.02/5.20      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 5.02/5.20      inference('simplify', [status(thm)], ['6'])).
% 5.02/5.20  thf('190', plain,
% 5.02/5.20      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 5.02/5.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.02/5.20  thf('191', plain, ((l1_pre_topc @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('192', plain, ((v2_pre_topc @ sk_B_3)),
% 5.02/5.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.20  thf('193', plain, ((v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 5.02/5.20      inference('demod', [status(thm)],
% 5.02/5.20                ['115', '116', '117', '143', '174', '175', '176', '177', 
% 5.02/5.20                 '178', '181', '182', '187', '188', '189', '190', '191', '192'])).
% 5.02/5.20  thf('194', plain, ($false), inference('demod', [status(thm)], ['58', '193'])).
% 5.02/5.20  
% 5.02/5.20  % SZS output end Refutation
% 5.02/5.20  
% 5.02/5.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
