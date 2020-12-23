%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M2x98ETjN1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:45 EST 2020

% Result     : Theorem 4.59s
% Output     : Refutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :  275 (3244 expanded)
%              Number of leaves         :   70 (1025 expanded)
%              Depth                    :   21
%              Number of atoms          : 1928 (46033 expanded)
%              Number of equality atoms :  100 ( 862 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X50: $i,X51: $i] :
      ( ( zip_tseitin_0 @ X50 @ X51 )
      | ( ( k2_struct_0 @ X50 )
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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
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

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
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
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ),
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
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X47: $i] :
      ( ( l1_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X47: $i] :
      ( ( l1_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_3 @ X0 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','31'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( l1_pre_topc @ X61 )
      | ~ ( zip_tseitin_0 @ X61 @ X62 )
      | ( zip_tseitin_2 @ X63 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X62 ) @ ( u1_struct_0 @ X61 ) ) ) )
      | ~ ( v1_funct_2 @ X63 @ ( u1_struct_0 @ X62 ) @ ( u1_struct_0 @ X61 ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X69: $i,X70: $i] :
      ( ~ ( v1_tdlat_3 @ X69 )
      | ( v3_pre_topc @ X70 @ X69 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X69 ) ) )
      | ~ ( l1_pre_topc @ X69 )
      | ~ ( v2_pre_topc @ X69 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ sk_A )
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
      ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X52: $i,X53: $i,X55: $i,X56: $i] :
      ( ( zip_tseitin_1 @ X52 @ X55 @ X53 @ X56 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X56 ) @ ( u1_struct_0 @ X53 ) @ X55 @ X52 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X57 @ X58 @ X59 ) @ X59 @ X58 @ X57 )
      | ( v5_pre_topc @ X59 @ X57 @ X58 )
      | ~ ( zip_tseitin_2 @ X59 @ X58 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_C_1 = k1_xboole_0 ),
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

thf('61',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( v2_pre_topc @ X64 )
      | ~ ( l1_pre_topc @ X64 )
      | ( m1_subset_1 @ ( sk_D_1 @ X65 @ X64 @ X66 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( v5_pre_topc @ X65 @ X66 @ X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X66 ) @ ( u1_struct_0 @ X64 ) ) ) )
      | ~ ( v1_funct_2 @ X65 @ ( u1_struct_0 @ X66 ) @ ( u1_struct_0 @ X64 ) )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( l1_pre_topc @ X66 )
      | ~ ( v2_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('62',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) )
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
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','67','68'])).

thf('70',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ),
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
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X50: $i,X51: $i] :
      ( ( zip_tseitin_0 @ X50 @ X51 )
      | ( ( k2_struct_0 @ X50 )
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
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ sk_B_3 ) @ X0 )
      | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_3 ) @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_3 ) @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( ( u1_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('89',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_3 ) @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ( ( u1_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('93',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('95',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B_3 ) @ ( k2_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('98',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
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
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['98','101'])).

thf('103',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('104',plain,
    ( ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('106',plain,(
    sk_C_1 = k1_xboole_0 ),
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
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( v2_pre_topc @ X64 )
      | ~ ( l1_pre_topc @ X64 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X66 @ ( k8_relset_1 @ ( u1_struct_0 @ X66 ) @ ( u1_struct_0 @ X64 ) @ X65 @ ( sk_D_1 @ X65 @ X64 @ X66 ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X66 ) @ ( u1_struct_0 @ X64 ) @ X65 @ ( k2_pre_topc @ X64 @ ( sk_D_1 @ X65 @ X64 @ X66 ) ) ) )
      | ( v5_pre_topc @ X65 @ X66 @ X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X66 ) @ ( u1_struct_0 @ X64 ) ) ) )
      | ~ ( v1_funct_2 @ X65 @ ( u1_struct_0 @ X66 ) @ ( u1_struct_0 @ X64 ) )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( l1_pre_topc @ X66 )
      | ~ ( v2_pre_topc @ X66 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k8_relset_1 @ X37 @ X38 @ X39 @ X38 )
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
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
    inference(simplify,[status(thm)],['5'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('125',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('126',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('130',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X42: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X42 ) @ X42 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

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
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_partfun1 @ X41 @ X40 )
      | ( ( k1_relat_1 @ X41 )
        = X40 )
      | ~ ( v4_relat_1 @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('136',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['135'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('137',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('138',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','138'])).

thf('140',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('141',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('142',plain,(
    ! [X44: $i,X45: $i] :
      ( m1_subset_1 @ ( sk_C @ X44 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('143',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','147'])).

thf('149',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X44: $i,X45: $i] :
      ( v4_relat_1 @ ( sk_C @ X44 @ X45 ) @ X45 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('152',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['139','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['120','154'])).

thf('156',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k8_relset_1 @ X37 @ X38 @ X39 @ X38 )
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('159',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('162',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['159','162'])).

thf('164',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_3 ) )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['156','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('166',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_3 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('168',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

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

thf('169',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = X48 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('170',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v4_pre_topc @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v4_pre_topc @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('174',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v1_tdlat_3 @ X71 )
      | ( v4_pre_topc @ X72 @ X71 )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X71 ) ) )
      | ~ ( l1_pre_topc @ X71 )
      | ~ ( v2_pre_topc @ X71 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('175',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k1_relat_1 @ sk_C_1 ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v4_pre_topc @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['172','179'])).

thf('181',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('182',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['139','152'])).

thf('183',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('184',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['139','152'])).

thf('185',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('187',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('188',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('191',plain,(
    ! [X44: $i,X45: $i] :
      ( v1_funct_1 @ ( sk_C @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('192',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('195',plain,(
    ! [X44: $i,X45: $i] :
      ( v1_funct_2 @ ( sk_C @ X44 @ X45 ) @ X45 @ X44 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('196',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('198',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('199',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('200',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ),
    inference(demod,[status(thm)],['115','116','117','155','185','186','187','188','189','192','193','196','197','198','199','200','201'])).

thf('203',plain,(
    $false ),
    inference(demod,[status(thm)],['58','202'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M2x98ETjN1
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.59/4.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.59/4.79  % Solved by: fo/fo7.sh
% 4.59/4.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.59/4.79  % done 5311 iterations in 4.327s
% 4.59/4.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.59/4.79  % SZS output start Refutation
% 4.59/4.79  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 4.59/4.79  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.59/4.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.59/4.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.59/4.79  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.59/4.79  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 4.59/4.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.59/4.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.59/4.79  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 4.59/4.79  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.59/4.79  thf(sk_A_type, type, sk_A: $i).
% 4.59/4.79  thf(sk_B_3_type, type, sk_B_3: $i).
% 4.59/4.79  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 4.59/4.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.59/4.79  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 4.59/4.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.59/4.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.59/4.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.59/4.79  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.59/4.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.59/4.79  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.59/4.79  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.59/4.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.59/4.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.59/4.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.59/4.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.59/4.79  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.59/4.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.59/4.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.59/4.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.59/4.79  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 4.59/4.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.59/4.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.59/4.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.59/4.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.59/4.79  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 4.59/4.79  thf(sk_B_type, type, sk_B: $i > $i).
% 4.59/4.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 4.59/4.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.59/4.79  thf(t68_tex_2, conjecture,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.59/4.79       ( ![B:$i]:
% 4.59/4.79         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.59/4.79           ( ![C:$i]:
% 4.59/4.79             ( ( ( v1_funct_1 @ C ) & 
% 4.59/4.79                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.59/4.79                 ( m1_subset_1 @
% 4.59/4.79                   C @ 
% 4.59/4.79                   ( k1_zfmisc_1 @
% 4.59/4.79                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.59/4.79               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 4.59/4.79  thf(zf_stmt_0, negated_conjecture,
% 4.59/4.79    (~( ![A:$i]:
% 4.59/4.79        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.59/4.79          ( ![B:$i]:
% 4.59/4.79            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.59/4.79              ( ![C:$i]:
% 4.59/4.79                ( ( ( v1_funct_1 @ C ) & 
% 4.59/4.79                    ( v1_funct_2 @
% 4.59/4.79                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.59/4.79                    ( m1_subset_1 @
% 4.59/4.79                      C @ 
% 4.59/4.79                      ( k1_zfmisc_1 @
% 4.59/4.79                        ( k2_zfmisc_1 @
% 4.59/4.79                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.59/4.79                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 4.59/4.79    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 4.59/4.79  thf('0', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf(t55_tops_2, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( l1_pre_topc @ A ) =>
% 4.59/4.79       ( ![B:$i]:
% 4.59/4.79         ( ( l1_pre_topc @ B ) =>
% 4.59/4.79           ( ![C:$i]:
% 4.59/4.79             ( ( ( m1_subset_1 @
% 4.59/4.79                   C @ 
% 4.59/4.79                   ( k1_zfmisc_1 @
% 4.59/4.79                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 4.59/4.79                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.59/4.79                 ( v1_funct_1 @ C ) ) =>
% 4.59/4.79               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 4.59/4.79                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.59/4.79                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.59/4.79                   ( ![D:$i]:
% 4.59/4.79                     ( ( m1_subset_1 @
% 4.59/4.79                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.59/4.79                       ( ( v3_pre_topc @ D @ B ) =>
% 4.59/4.79                         ( v3_pre_topc @
% 4.59/4.79                           ( k8_relset_1 @
% 4.59/4.79                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.59/4.79                           A ) ) ) ) ) ) ) ) ) ) ))).
% 4.59/4.79  thf(zf_stmt_1, axiom,
% 4.59/4.79    (![B:$i,A:$i]:
% 4.59/4.79     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 4.59/4.79         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.59/4.79       ( zip_tseitin_0 @ B @ A ) ))).
% 4.59/4.79  thf('1', plain,
% 4.59/4.79      (![X50 : $i, X51 : $i]:
% 4.59/4.79         ((zip_tseitin_0 @ X50 @ X51) | ((k2_struct_0 @ X50) = (k1_xboole_0)))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.59/4.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.59/4.79  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.59/4.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.59/4.79  thf('3', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 4.59/4.79      inference('sup+', [status(thm)], ['1', '2'])).
% 4.59/4.79  thf(l13_xboole_0, axiom,
% 4.59/4.79    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.59/4.79  thf('4', plain,
% 4.59/4.79      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 4.59/4.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.59/4.79  thf(t113_zfmisc_1, axiom,
% 4.59/4.79    (![A:$i,B:$i]:
% 4.59/4.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.59/4.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.59/4.79  thf('5', plain,
% 4.59/4.79      (![X11 : $i, X12 : $i]:
% 4.59/4.79         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 4.59/4.79          | ((X12) != (k1_xboole_0)))),
% 4.59/4.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.59/4.79  thf('6', plain,
% 4.59/4.79      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('simplify', [status(thm)], ['5'])).
% 4.59/4.79  thf('7', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.59/4.79      inference('sup+', [status(thm)], ['4', '6'])).
% 4.59/4.79  thf(d3_struct_0, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.59/4.79  thf('8', plain,
% 4.59/4.79      (![X46 : $i]:
% 4.59/4.79         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 4.59/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.59/4.79  thf('9', plain,
% 4.59/4.79      (![X46 : $i]:
% 4.59/4.79         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 4.59/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.59/4.79  thf('10', plain,
% 4.59/4.79      ((m1_subset_1 @ sk_C_1 @ 
% 4.59/4.79        (k1_zfmisc_1 @ 
% 4.59/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf(t3_subset, axiom,
% 4.59/4.79    (![A:$i,B:$i]:
% 4.59/4.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.59/4.79  thf('11', plain,
% 4.59/4.79      (![X16 : $i, X17 : $i]:
% 4.59/4.79         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 4.59/4.79      inference('cnf', [status(esa)], [t3_subset])).
% 4.59/4.79  thf('12', plain,
% 4.59/4.79      ((r1_tarski @ sk_C_1 @ 
% 4.59/4.79        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['10', '11'])).
% 4.59/4.79  thf('13', plain,
% 4.59/4.79      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 4.59/4.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.59/4.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.59/4.79  thf('14', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 4.59/4.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.59/4.79  thf(d10_xboole_0, axiom,
% 4.59/4.79    (![A:$i,B:$i]:
% 4.59/4.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.59/4.79  thf('15', plain,
% 4.59/4.79      (![X4 : $i, X6 : $i]:
% 4.59/4.79         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.59/4.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.59/4.79  thf('16', plain,
% 4.59/4.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['14', '15'])).
% 4.59/4.79  thf('17', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         (~ (r1_tarski @ X1 @ X0)
% 4.59/4.79          | ~ (v1_xboole_0 @ X0)
% 4.59/4.79          | ((X1) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['13', '16'])).
% 4.59/4.79  thf('18', plain,
% 4.59/4.79      ((((sk_C_1) = (k1_xboole_0))
% 4.59/4.79        | ~ (v1_xboole_0 @ 
% 4.59/4.79             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.59/4.79      inference('sup-', [status(thm)], ['12', '17'])).
% 4.59/4.79  thf('19', plain,
% 4.59/4.79      ((~ (v1_xboole_0 @ 
% 4.59/4.79           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))
% 4.59/4.79        | ~ (l1_struct_0 @ sk_A)
% 4.59/4.79        | ((sk_C_1) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['9', '18'])).
% 4.59/4.79  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf(dt_l1_pre_topc, axiom,
% 4.59/4.79    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 4.59/4.79  thf('21', plain,
% 4.59/4.79      (![X47 : $i]: ((l1_struct_0 @ X47) | ~ (l1_pre_topc @ X47))),
% 4.59/4.79      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.59/4.79  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 4.59/4.79      inference('sup-', [status(thm)], ['20', '21'])).
% 4.59/4.79  thf('23', plain,
% 4.59/4.79      ((~ (v1_xboole_0 @ 
% 4.59/4.79           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))
% 4.59/4.79        | ((sk_C_1) = (k1_xboole_0)))),
% 4.59/4.79      inference('demod', [status(thm)], ['19', '22'])).
% 4.59/4.79  thf('24', plain,
% 4.59/4.79      ((~ (v1_xboole_0 @ 
% 4.59/4.79           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_3)))
% 4.59/4.79        | ~ (l1_struct_0 @ sk_B_3)
% 4.59/4.79        | ((sk_C_1) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['8', '23'])).
% 4.59/4.79  thf('25', plain, ((l1_pre_topc @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('26', plain,
% 4.59/4.79      (![X47 : $i]: ((l1_struct_0 @ X47) | ~ (l1_pre_topc @ X47))),
% 4.59/4.79      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.59/4.79  thf('27', plain, ((l1_struct_0 @ sk_B_3)),
% 4.59/4.79      inference('sup-', [status(thm)], ['25', '26'])).
% 4.59/4.79  thf('28', plain,
% 4.59/4.79      ((~ (v1_xboole_0 @ 
% 4.59/4.79           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_3)))
% 4.59/4.79        | ((sk_C_1) = (k1_xboole_0)))),
% 4.59/4.79      inference('demod', [status(thm)], ['24', '27'])).
% 4.59/4.79  thf('29', plain,
% 4.59/4.79      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.59/4.79        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 4.59/4.79        | ((sk_C_1) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['7', '28'])).
% 4.59/4.79  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.59/4.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.59/4.79  thf('31', plain,
% 4.59/4.79      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3)) | ((sk_C_1) = (k1_xboole_0)))),
% 4.59/4.79      inference('demod', [status(thm)], ['29', '30'])).
% 4.59/4.79  thf('32', plain,
% 4.59/4.79      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_3 @ X0) | ((sk_C_1) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['3', '31'])).
% 4.59/4.79  thf('33', plain,
% 4.59/4.79      ((m1_subset_1 @ sk_C_1 @ 
% 4.59/4.79        (k1_zfmisc_1 @ 
% 4.59/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 4.59/4.79  thf(zf_stmt_3, axiom,
% 4.59/4.79    (![C:$i,B:$i,A:$i]:
% 4.59/4.79     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 4.59/4.79       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.59/4.79         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 4.59/4.79  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 4.59/4.79  thf(zf_stmt_5, axiom,
% 4.59/4.79    (![D:$i,C:$i,B:$i,A:$i]:
% 4.59/4.79     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 4.59/4.79       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.59/4.79         ( ( v3_pre_topc @ D @ B ) =>
% 4.59/4.79           ( v3_pre_topc @
% 4.59/4.79             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.59/4.79             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 4.59/4.79  thf(zf_stmt_7, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( l1_pre_topc @ A ) =>
% 4.59/4.79       ( ![B:$i]:
% 4.59/4.79         ( ( l1_pre_topc @ B ) =>
% 4.59/4.79           ( ![C:$i]:
% 4.59/4.79             ( ( ( v1_funct_1 @ C ) & 
% 4.59/4.79                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.59/4.79                 ( m1_subset_1 @
% 4.59/4.79                   C @ 
% 4.59/4.79                   ( k1_zfmisc_1 @
% 4.59/4.79                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.59/4.79               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 4.59/4.79  thf('34', plain,
% 4.59/4.79      (![X61 : $i, X62 : $i, X63 : $i]:
% 4.59/4.79         (~ (l1_pre_topc @ X61)
% 4.59/4.79          | ~ (zip_tseitin_0 @ X61 @ X62)
% 4.59/4.79          | (zip_tseitin_2 @ X63 @ X61 @ X62)
% 4.59/4.79          | ~ (m1_subset_1 @ X63 @ 
% 4.59/4.79               (k1_zfmisc_1 @ 
% 4.59/4.79                (k2_zfmisc_1 @ (u1_struct_0 @ X62) @ (u1_struct_0 @ X61))))
% 4.59/4.79          | ~ (v1_funct_2 @ X63 @ (u1_struct_0 @ X62) @ (u1_struct_0 @ X61))
% 4.59/4.79          | ~ (v1_funct_1 @ X63)
% 4.59/4.79          | ~ (l1_pre_topc @ X62))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_7])).
% 4.59/4.79  thf('35', plain,
% 4.59/4.79      ((~ (l1_pre_topc @ sk_A)
% 4.59/4.79        | ~ (v1_funct_1 @ sk_C_1)
% 4.59/4.79        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.59/4.79             (u1_struct_0 @ sk_B_3))
% 4.59/4.79        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.59/4.79        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A)
% 4.59/4.79        | ~ (l1_pre_topc @ sk_B_3))),
% 4.59/4.79      inference('sup-', [status(thm)], ['33', '34'])).
% 4.59/4.79  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('38', plain,
% 4.59/4.79      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('39', plain, ((l1_pre_topc @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('40', plain,
% 4.59/4.79      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.59/4.79        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 4.59/4.79  thf('41', plain,
% 4.59/4.79      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('sup-', [status(thm)], ['32', '40'])).
% 4.59/4.79  thf('42', plain,
% 4.59/4.79      ((m1_subset_1 @ sk_C_1 @ 
% 4.59/4.79        (k1_zfmisc_1 @ 
% 4.59/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf(dt_k8_relset_1, axiom,
% 4.59/4.79    (![A:$i,B:$i,C:$i,D:$i]:
% 4.59/4.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.59/4.79       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.59/4.79  thf('43', plain,
% 4.59/4.79      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.59/4.79         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.59/4.79          | (m1_subset_1 @ (k8_relset_1 @ X31 @ X32 @ X30 @ X33) @ 
% 4.59/4.79             (k1_zfmisc_1 @ X31)))),
% 4.59/4.79      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 4.59/4.79  thf('44', plain,
% 4.59/4.79      (![X0 : $i]:
% 4.59/4.79         (m1_subset_1 @ 
% 4.59/4.79          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79           sk_C_1 @ X0) @ 
% 4.59/4.79          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['42', '43'])).
% 4.59/4.79  thf(t17_tdlat_3, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.59/4.79       ( ( v1_tdlat_3 @ A ) <=>
% 4.59/4.79         ( ![B:$i]:
% 4.59/4.79           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.59/4.79             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 4.59/4.79  thf('45', plain,
% 4.59/4.79      (![X69 : $i, X70 : $i]:
% 4.59/4.79         (~ (v1_tdlat_3 @ X69)
% 4.59/4.79          | (v3_pre_topc @ X70 @ X69)
% 4.59/4.79          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 4.59/4.79          | ~ (l1_pre_topc @ X69)
% 4.59/4.79          | ~ (v2_pre_topc @ X69))),
% 4.59/4.79      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 4.59/4.79  thf('46', plain,
% 4.59/4.79      (![X0 : $i]:
% 4.59/4.79         (~ (v2_pre_topc @ sk_A)
% 4.59/4.79          | ~ (l1_pre_topc @ sk_A)
% 4.59/4.79          | (v3_pre_topc @ 
% 4.59/4.79             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79              sk_C_1 @ X0) @ 
% 4.59/4.79             sk_A)
% 4.59/4.79          | ~ (v1_tdlat_3 @ sk_A))),
% 4.59/4.79      inference('sup-', [status(thm)], ['44', '45'])).
% 4.59/4.79  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('49', plain, ((v1_tdlat_3 @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('50', plain,
% 4.59/4.79      (![X0 : $i]:
% 4.59/4.79         (v3_pre_topc @ 
% 4.59/4.79          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79           sk_C_1 @ X0) @ 
% 4.59/4.79          sk_A)),
% 4.59/4.79      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 4.59/4.79  thf('51', plain,
% 4.59/4.79      (![X52 : $i, X53 : $i, X55 : $i, X56 : $i]:
% 4.59/4.79         ((zip_tseitin_1 @ X52 @ X55 @ X53 @ X56)
% 4.59/4.79          | ~ (v3_pre_topc @ 
% 4.59/4.79               (k8_relset_1 @ (u1_struct_0 @ X56) @ (u1_struct_0 @ X53) @ 
% 4.59/4.79                X55 @ X52) @ 
% 4.59/4.79               X56))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.59/4.79  thf('52', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 4.59/4.79      inference('sup-', [status(thm)], ['50', '51'])).
% 4.59/4.79  thf('53', plain,
% 4.59/4.79      (![X57 : $i, X58 : $i, X59 : $i]:
% 4.59/4.79         (~ (zip_tseitin_1 @ (sk_D @ X57 @ X58 @ X59) @ X59 @ X58 @ X57)
% 4.59/4.79          | (v5_pre_topc @ X59 @ X57 @ X58)
% 4.59/4.79          | ~ (zip_tseitin_2 @ X59 @ X58 @ X57))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.59/4.79  thf('54', plain,
% 4.59/4.79      ((~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.59/4.79        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3))),
% 4.59/4.79      inference('sup-', [status(thm)], ['52', '53'])).
% 4.59/4.79  thf('55', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('56', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 4.59/4.79      inference('clc', [status(thm)], ['54', '55'])).
% 4.59/4.79  thf('57', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['41', '56'])).
% 4.59/4.79  thf('58', plain, (~ (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 4.59/4.79      inference('demod', [status(thm)], ['0', '57'])).
% 4.59/4.79  thf(d1_xboole_0, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.59/4.79  thf('59', plain,
% 4.59/4.79      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.59/4.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.59/4.79  thf('60', plain,
% 4.59/4.79      ((m1_subset_1 @ sk_C_1 @ 
% 4.59/4.79        (k1_zfmisc_1 @ 
% 4.59/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf(t56_tops_2, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.59/4.79       ( ![B:$i]:
% 4.59/4.79         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.59/4.79           ( ![C:$i]:
% 4.59/4.79             ( ( ( v1_funct_1 @ C ) & 
% 4.59/4.79                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.59/4.79                 ( m1_subset_1 @
% 4.59/4.79                   C @ 
% 4.59/4.79                   ( k1_zfmisc_1 @
% 4.59/4.79                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.59/4.79               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.59/4.79                 ( ![D:$i]:
% 4.59/4.79                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.59/4.79                     ( r1_tarski @
% 4.59/4.79                       ( k2_pre_topc @
% 4.59/4.79                         A @ 
% 4.59/4.79                         ( k8_relset_1 @
% 4.59/4.79                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 4.59/4.79                       ( k8_relset_1 @
% 4.59/4.79                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 4.59/4.79                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 4.59/4.79  thf('61', plain,
% 4.59/4.79      (![X64 : $i, X65 : $i, X66 : $i]:
% 4.59/4.79         (~ (v2_pre_topc @ X64)
% 4.59/4.79          | ~ (l1_pre_topc @ X64)
% 4.59/4.79          | (m1_subset_1 @ (sk_D_1 @ X65 @ X64 @ X66) @ 
% 4.59/4.79             (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 4.59/4.79          | (v5_pre_topc @ X65 @ X66 @ X64)
% 4.59/4.79          | ~ (m1_subset_1 @ X65 @ 
% 4.59/4.79               (k1_zfmisc_1 @ 
% 4.59/4.79                (k2_zfmisc_1 @ (u1_struct_0 @ X66) @ (u1_struct_0 @ X64))))
% 4.59/4.79          | ~ (v1_funct_2 @ X65 @ (u1_struct_0 @ X66) @ (u1_struct_0 @ X64))
% 4.59/4.79          | ~ (v1_funct_1 @ X65)
% 4.59/4.79          | ~ (l1_pre_topc @ X66)
% 4.59/4.79          | ~ (v2_pre_topc @ X66))),
% 4.59/4.79      inference('cnf', [status(esa)], [t56_tops_2])).
% 4.59/4.79  thf('62', plain,
% 4.59/4.79      ((~ (v2_pre_topc @ sk_A)
% 4.59/4.79        | ~ (l1_pre_topc @ sk_A)
% 4.59/4.79        | ~ (v1_funct_1 @ sk_C_1)
% 4.59/4.79        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.59/4.79             (u1_struct_0 @ sk_B_3))
% 4.59/4.79        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)
% 4.59/4.79        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.59/4.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))
% 4.59/4.79        | ~ (l1_pre_topc @ sk_B_3)
% 4.59/4.79        | ~ (v2_pre_topc @ sk_B_3))),
% 4.59/4.79      inference('sup-', [status(thm)], ['60', '61'])).
% 4.59/4.79  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('65', plain, ((v1_funct_1 @ sk_C_1)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('66', plain,
% 4.59/4.79      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('67', plain, ((l1_pre_topc @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('68', plain, ((v2_pre_topc @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('69', plain,
% 4.59/4.79      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)
% 4.59/4.79        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.59/4.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3))))),
% 4.59/4.79      inference('demod', [status(thm)],
% 4.59/4.79                ['62', '63', '64', '65', '66', '67', '68'])).
% 4.59/4.79  thf('70', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('71', plain,
% 4.59/4.79      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.59/4.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 4.59/4.79      inference('clc', [status(thm)], ['69', '70'])).
% 4.59/4.79  thf(t5_subset, axiom,
% 4.59/4.79    (![A:$i,B:$i,C:$i]:
% 4.59/4.79     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 4.59/4.79          ( v1_xboole_0 @ C ) ) ))).
% 4.59/4.79  thf('72', plain,
% 4.59/4.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.59/4.79         (~ (r2_hidden @ X22 @ X23)
% 4.59/4.79          | ~ (v1_xboole_0 @ X24)
% 4.59/4.79          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 4.59/4.79      inference('cnf', [status(esa)], [t5_subset])).
% 4.59/4.79  thf('73', plain,
% 4.59/4.79      (![X0 : $i]:
% 4.59/4.79         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 4.59/4.79          | ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['71', '72'])).
% 4.59/4.79  thf('74', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['41', '56'])).
% 4.59/4.79  thf('75', plain,
% 4.59/4.79      (![X0 : $i]:
% 4.59/4.79         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 4.59/4.79          | ~ (r2_hidden @ X0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A)))),
% 4.59/4.79      inference('demod', [status(thm)], ['73', '74'])).
% 4.59/4.79  thf('76', plain,
% 4.59/4.79      (![X50 : $i, X51 : $i]:
% 4.59/4.79         ((zip_tseitin_0 @ X50 @ X51) | ((k2_struct_0 @ X50) = (k1_xboole_0)))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.59/4.79  thf('77', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 4.59/4.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.59/4.79  thf('78', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.59/4.79         ((r1_tarski @ (k2_struct_0 @ X0) @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 4.59/4.79      inference('sup+', [status(thm)], ['76', '77'])).
% 4.59/4.79  thf('79', plain,
% 4.59/4.79      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.59/4.79        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 4.59/4.79  thf('80', plain,
% 4.59/4.79      (![X0 : $i]:
% 4.59/4.79         ((r1_tarski @ (k2_struct_0 @ sk_B_3) @ X0)
% 4.59/4.79          | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('sup-', [status(thm)], ['78', '79'])).
% 4.59/4.79  thf('81', plain,
% 4.59/4.79      (![X46 : $i]:
% 4.59/4.79         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 4.59/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.59/4.79  thf('82', plain,
% 4.59/4.79      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.59/4.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 4.59/4.79      inference('clc', [status(thm)], ['69', '70'])).
% 4.59/4.79  thf('83', plain,
% 4.59/4.79      (![X16 : $i, X17 : $i]:
% 4.59/4.79         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 4.59/4.79      inference('cnf', [status(esa)], [t3_subset])).
% 4.59/4.79  thf('84', plain,
% 4.59/4.79      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.59/4.79      inference('sup-', [status(thm)], ['82', '83'])).
% 4.59/4.79  thf('85', plain,
% 4.59/4.79      (![X4 : $i, X6 : $i]:
% 4.59/4.79         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.59/4.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.59/4.79  thf('86', plain,
% 4.59/4.79      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79           (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A))
% 4.59/4.79        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['84', '85'])).
% 4.59/4.79  thf('87', plain,
% 4.59/4.79      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_3) @ 
% 4.59/4.79           (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A))
% 4.59/4.79        | ~ (l1_struct_0 @ sk_B_3)
% 4.59/4.79        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['81', '86'])).
% 4.59/4.79  thf('88', plain, ((l1_struct_0 @ sk_B_3)),
% 4.59/4.79      inference('sup-', [status(thm)], ['25', '26'])).
% 4.59/4.79  thf('89', plain,
% 4.59/4.79      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_3) @ 
% 4.59/4.79           (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A))
% 4.59/4.79        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 4.59/4.79      inference('demod', [status(thm)], ['87', '88'])).
% 4.59/4.79  thf('90', plain,
% 4.59/4.79      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.59/4.79        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['80', '89'])).
% 4.59/4.79  thf('91', plain,
% 4.59/4.79      (![X46 : $i]:
% 4.59/4.79         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 4.59/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.59/4.79  thf('92', plain,
% 4.59/4.79      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.59/4.79      inference('sup-', [status(thm)], ['82', '83'])).
% 4.59/4.79  thf('93', plain,
% 4.59/4.79      (((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (k2_struct_0 @ sk_B_3))
% 4.59/4.79        | ~ (l1_struct_0 @ sk_B_3))),
% 4.59/4.79      inference('sup+', [status(thm)], ['91', '92'])).
% 4.59/4.79  thf('94', plain, ((l1_struct_0 @ sk_B_3)),
% 4.59/4.79      inference('sup-', [status(thm)], ['25', '26'])).
% 4.59/4.79  thf('95', plain,
% 4.59/4.79      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (k2_struct_0 @ sk_B_3))),
% 4.59/4.79      inference('demod', [status(thm)], ['93', '94'])).
% 4.59/4.79  thf('96', plain,
% 4.59/4.79      (((r1_tarski @ (u1_struct_0 @ sk_B_3) @ (k2_struct_0 @ sk_B_3))
% 4.59/4.79        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('sup+', [status(thm)], ['90', '95'])).
% 4.59/4.79  thf('97', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         (~ (r1_tarski @ X1 @ X0)
% 4.59/4.79          | ~ (v1_xboole_0 @ X0)
% 4.59/4.79          | ((X1) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['13', '16'])).
% 4.59/4.79  thf('98', plain,
% 4.59/4.79      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.59/4.79        | ((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 4.59/4.79        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['96', '97'])).
% 4.59/4.79  thf('99', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 4.59/4.79      inference('sup+', [status(thm)], ['1', '2'])).
% 4.59/4.79  thf('100', plain,
% 4.59/4.79      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.59/4.79        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 4.59/4.79  thf('101', plain,
% 4.59/4.79      (((v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 4.59/4.79        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('sup-', [status(thm)], ['99', '100'])).
% 4.59/4.79  thf('102', plain,
% 4.59/4.79      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 4.59/4.79        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('clc', [status(thm)], ['98', '101'])).
% 4.59/4.79  thf('103', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['41', '56'])).
% 4.59/4.79  thf('104', plain,
% 4.59/4.79      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 4.59/4.79        | (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('demod', [status(thm)], ['102', '103'])).
% 4.59/4.79  thf('105', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 4.59/4.79      inference('clc', [status(thm)], ['54', '55'])).
% 4.59/4.79  thf('106', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['41', '56'])).
% 4.59/4.79  thf('107', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)),
% 4.59/4.79      inference('demod', [status(thm)], ['105', '106'])).
% 4.59/4.79  thf('108', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.59/4.79      inference('clc', [status(thm)], ['104', '107'])).
% 4.59/4.79  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.59/4.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.59/4.79  thf('110', plain,
% 4.59/4.79      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('demod', [status(thm)], ['75', '108', '109'])).
% 4.59/4.79  thf('111', plain, ((v1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 4.59/4.79      inference('sup-', [status(thm)], ['59', '110'])).
% 4.59/4.79  thf('112', plain,
% 4.59/4.79      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 4.59/4.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.59/4.79  thf('113', plain, (((sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['111', '112'])).
% 4.59/4.79  thf('114', plain,
% 4.59/4.79      (![X64 : $i, X65 : $i, X66 : $i]:
% 4.59/4.79         (~ (v2_pre_topc @ X64)
% 4.59/4.79          | ~ (l1_pre_topc @ X64)
% 4.59/4.79          | ~ (r1_tarski @ 
% 4.59/4.79               (k2_pre_topc @ X66 @ 
% 4.59/4.79                (k8_relset_1 @ (u1_struct_0 @ X66) @ (u1_struct_0 @ X64) @ 
% 4.59/4.79                 X65 @ (sk_D_1 @ X65 @ X64 @ X66))) @ 
% 4.59/4.79               (k8_relset_1 @ (u1_struct_0 @ X66) @ (u1_struct_0 @ X64) @ 
% 4.59/4.79                X65 @ (k2_pre_topc @ X64 @ (sk_D_1 @ X65 @ X64 @ X66))))
% 4.59/4.79          | (v5_pre_topc @ X65 @ X66 @ X64)
% 4.59/4.79          | ~ (m1_subset_1 @ X65 @ 
% 4.59/4.79               (k1_zfmisc_1 @ 
% 4.59/4.79                (k2_zfmisc_1 @ (u1_struct_0 @ X66) @ (u1_struct_0 @ X64))))
% 4.59/4.79          | ~ (v1_funct_2 @ X65 @ (u1_struct_0 @ X66) @ (u1_struct_0 @ X64))
% 4.59/4.79          | ~ (v1_funct_1 @ X65)
% 4.59/4.79          | ~ (l1_pre_topc @ X66)
% 4.59/4.79          | ~ (v2_pre_topc @ X66))),
% 4.59/4.79      inference('cnf', [status(esa)], [t56_tops_2])).
% 4.59/4.79  thf('115', plain,
% 4.59/4.79      ((~ (r1_tarski @ 
% 4.59/4.79           (k2_pre_topc @ sk_A @ 
% 4.59/4.79            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79             k1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))) @ 
% 4.59/4.79           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79            k1_xboole_0 @ (k2_pre_topc @ sk_B_3 @ k1_xboole_0)))
% 4.59/4.79        | ~ (v2_pre_topc @ sk_A)
% 4.59/4.79        | ~ (l1_pre_topc @ sk_A)
% 4.59/4.79        | ~ (v1_funct_1 @ k1_xboole_0)
% 4.59/4.79        | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 4.59/4.79             (u1_struct_0 @ sk_B_3))
% 4.59/4.79        | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.59/4.79             (k1_zfmisc_1 @ 
% 4.59/4.79              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))
% 4.59/4.79        | (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)
% 4.59/4.79        | ~ (l1_pre_topc @ sk_B_3)
% 4.59/4.79        | ~ (v2_pre_topc @ sk_B_3))),
% 4.59/4.79      inference('sup-', [status(thm)], ['113', '114'])).
% 4.59/4.79  thf('116', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.59/4.79      inference('clc', [status(thm)], ['104', '107'])).
% 4.59/4.79  thf('117', plain, (((sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['111', '112'])).
% 4.59/4.79  thf(t4_subset_1, axiom,
% 4.59/4.79    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.59/4.79  thf('118', plain,
% 4.59/4.79      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 4.59/4.79      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.59/4.79  thf(t38_relset_1, axiom,
% 4.59/4.79    (![A:$i,B:$i,C:$i]:
% 4.59/4.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.59/4.79       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 4.59/4.79         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.59/4.79  thf('119', plain,
% 4.59/4.79      (![X37 : $i, X38 : $i, X39 : $i]:
% 4.59/4.79         (((k8_relset_1 @ X37 @ X38 @ X39 @ X38)
% 4.59/4.79            = (k1_relset_1 @ X37 @ X38 @ X39))
% 4.59/4.79          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 4.59/4.79      inference('cnf', [status(esa)], [t38_relset_1])).
% 4.59/4.79  thf('120', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 4.59/4.79           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['118', '119'])).
% 4.59/4.79  thf('121', plain,
% 4.59/4.79      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 4.59/4.79      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.59/4.79  thf(redefinition_k1_relset_1, axiom,
% 4.59/4.79    (![A:$i,B:$i,C:$i]:
% 4.59/4.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.59/4.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.59/4.79  thf('122', plain,
% 4.59/4.79      (![X34 : $i, X35 : $i, X36 : $i]:
% 4.59/4.79         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 4.59/4.79          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 4.59/4.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.59/4.79  thf('123', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['121', '122'])).
% 4.59/4.79  thf('124', plain,
% 4.59/4.79      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('simplify', [status(thm)], ['5'])).
% 4.59/4.79  thf(dt_k6_partfun1, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( m1_subset_1 @
% 4.59/4.79         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.59/4.79       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.59/4.79  thf('125', plain,
% 4.59/4.79      (![X43 : $i]:
% 4.59/4.79         (m1_subset_1 @ (k6_partfun1 @ X43) @ 
% 4.59/4.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 4.59/4.79      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.59/4.79  thf('126', plain,
% 4.59/4.79      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.59/4.79      inference('sup+', [status(thm)], ['124', '125'])).
% 4.59/4.79  thf('127', plain,
% 4.59/4.79      (![X16 : $i, X17 : $i]:
% 4.59/4.79         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 4.59/4.79      inference('cnf', [status(esa)], [t3_subset])).
% 4.59/4.79  thf('128', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 4.59/4.79      inference('sup-', [status(thm)], ['126', '127'])).
% 4.59/4.79  thf('129', plain,
% 4.59/4.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['14', '15'])).
% 4.59/4.79  thf('130', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['128', '129'])).
% 4.59/4.79  thf('131', plain, (![X42 : $i]: (v1_partfun1 @ (k6_partfun1 @ X42) @ X42)),
% 4.59/4.79      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.59/4.79  thf('132', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 4.59/4.79      inference('sup+', [status(thm)], ['130', '131'])).
% 4.59/4.79  thf(d4_partfun1, axiom,
% 4.59/4.79    (![A:$i,B:$i]:
% 4.59/4.79     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.59/4.79       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 4.59/4.79  thf('133', plain,
% 4.59/4.79      (![X40 : $i, X41 : $i]:
% 4.59/4.79         (~ (v1_partfun1 @ X41 @ X40)
% 4.59/4.79          | ((k1_relat_1 @ X41) = (X40))
% 4.59/4.79          | ~ (v4_relat_1 @ X41 @ X40)
% 4.59/4.79          | ~ (v1_relat_1 @ X41))),
% 4.59/4.79      inference('cnf', [status(esa)], [d4_partfun1])).
% 4.59/4.79  thf('134', plain,
% 4.59/4.79      ((~ (v1_relat_1 @ k1_xboole_0)
% 4.59/4.79        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 4.59/4.79        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['132', '133'])).
% 4.59/4.79  thf('135', plain,
% 4.59/4.79      (![X11 : $i, X12 : $i]:
% 4.59/4.79         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 4.59/4.79          | ((X11) != (k1_xboole_0)))),
% 4.59/4.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.59/4.79  thf('136', plain,
% 4.59/4.79      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 4.59/4.79      inference('simplify', [status(thm)], ['135'])).
% 4.59/4.79  thf(fc6_relat_1, axiom,
% 4.59/4.79    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.59/4.79  thf('137', plain,
% 4.59/4.79      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 4.59/4.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.59/4.79  thf('138', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.59/4.79      inference('sup+', [status(thm)], ['136', '137'])).
% 4.59/4.79  thf('139', plain,
% 4.59/4.79      ((~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 4.59/4.79        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.59/4.79      inference('demod', [status(thm)], ['134', '138'])).
% 4.59/4.79  thf('140', plain,
% 4.59/4.79      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.59/4.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.59/4.79  thf('141', plain,
% 4.59/4.79      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('simplify', [status(thm)], ['5'])).
% 4.59/4.79  thf(rc1_funct_2, axiom,
% 4.59/4.79    (![A:$i,B:$i]:
% 4.59/4.79     ( ?[C:$i]:
% 4.59/4.79       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 4.59/4.79         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 4.59/4.79         ( v1_relat_1 @ C ) & 
% 4.59/4.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.59/4.79  thf('142', plain,
% 4.59/4.79      (![X44 : $i, X45 : $i]:
% 4.59/4.79         (m1_subset_1 @ (sk_C @ X44 @ X45) @ 
% 4.59/4.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))),
% 4.59/4.79      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.59/4.79  thf('143', plain,
% 4.59/4.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.59/4.79         (~ (r2_hidden @ X22 @ X23)
% 4.59/4.79          | ~ (v1_xboole_0 @ X24)
% 4.59/4.79          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 4.59/4.79      inference('cnf', [status(esa)], [t5_subset])).
% 4.59/4.79  thf('144', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.59/4.79         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 4.59/4.79          | ~ (r2_hidden @ X2 @ (sk_C @ X0 @ X1)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['142', '143'])).
% 4.59/4.79  thf('145', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.59/4.79          | ~ (r2_hidden @ X1 @ (sk_C @ k1_xboole_0 @ X0)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['141', '144'])).
% 4.59/4.79  thf('146', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.59/4.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.59/4.79  thf('147', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (sk_C @ k1_xboole_0 @ X0))),
% 4.59/4.79      inference('demod', [status(thm)], ['145', '146'])).
% 4.59/4.79  thf('148', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['140', '147'])).
% 4.59/4.79  thf('149', plain,
% 4.59/4.79      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 4.59/4.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.59/4.79  thf('150', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['148', '149'])).
% 4.59/4.79  thf('151', plain,
% 4.59/4.79      (![X44 : $i, X45 : $i]: (v4_relat_1 @ (sk_C @ X44 @ X45) @ X45)),
% 4.59/4.79      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.59/4.79  thf('152', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 4.59/4.79      inference('sup+', [status(thm)], ['150', '151'])).
% 4.59/4.79  thf('153', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('demod', [status(thm)], ['139', '152'])).
% 4.59/4.79  thf('154', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('demod', [status(thm)], ['123', '153'])).
% 4.59/4.79  thf('155', plain,
% 4.59/4.79      (![X0 : $i, X1 : $i]:
% 4.59/4.79         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.59/4.79      inference('demod', [status(thm)], ['120', '154'])).
% 4.59/4.79  thf('156', plain,
% 4.59/4.79      (![X46 : $i]:
% 4.59/4.79         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 4.59/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.59/4.79  thf('157', plain,
% 4.59/4.79      ((m1_subset_1 @ sk_C_1 @ 
% 4.59/4.79        (k1_zfmisc_1 @ 
% 4.59/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('158', plain,
% 4.59/4.79      (![X37 : $i, X38 : $i, X39 : $i]:
% 4.59/4.79         (((k8_relset_1 @ X37 @ X38 @ X39 @ X38)
% 4.59/4.79            = (k1_relset_1 @ X37 @ X38 @ X39))
% 4.59/4.79          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 4.59/4.79      inference('cnf', [status(esa)], [t38_relset_1])).
% 4.59/4.79  thf('159', plain,
% 4.59/4.79      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79         sk_C_1 @ (u1_struct_0 @ sk_B_3))
% 4.59/4.79         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79            sk_C_1))),
% 4.59/4.79      inference('sup-', [status(thm)], ['157', '158'])).
% 4.59/4.79  thf('160', plain,
% 4.59/4.79      ((m1_subset_1 @ sk_C_1 @ 
% 4.59/4.79        (k1_zfmisc_1 @ 
% 4.59/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('161', plain,
% 4.59/4.79      (![X34 : $i, X35 : $i, X36 : $i]:
% 4.59/4.79         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 4.59/4.79          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 4.59/4.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.59/4.79  thf('162', plain,
% 4.59/4.79      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 4.59/4.79         = (k1_relat_1 @ sk_C_1))),
% 4.59/4.79      inference('sup-', [status(thm)], ['160', '161'])).
% 4.59/4.79  thf('163', plain,
% 4.59/4.79      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79         sk_C_1 @ (u1_struct_0 @ sk_B_3)) = (k1_relat_1 @ sk_C_1))),
% 4.59/4.79      inference('demod', [status(thm)], ['159', '162'])).
% 4.59/4.79  thf('164', plain,
% 4.59/4.79      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79          sk_C_1 @ (k2_struct_0 @ sk_B_3)) = (k1_relat_1 @ sk_C_1))
% 4.59/4.79        | ~ (l1_struct_0 @ sk_B_3))),
% 4.59/4.79      inference('sup+', [status(thm)], ['156', '163'])).
% 4.59/4.79  thf('165', plain, ((l1_struct_0 @ sk_B_3)),
% 4.59/4.79      inference('sup-', [status(thm)], ['25', '26'])).
% 4.59/4.79  thf('166', plain,
% 4.59/4.79      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79         sk_C_1 @ (k2_struct_0 @ sk_B_3)) = (k1_relat_1 @ sk_C_1))),
% 4.59/4.79      inference('demod', [status(thm)], ['164', '165'])).
% 4.59/4.79  thf('167', plain,
% 4.59/4.79      (![X0 : $i]:
% 4.59/4.79         (m1_subset_1 @ 
% 4.59/4.79          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.59/4.79           sk_C_1 @ X0) @ 
% 4.59/4.79          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.59/4.79      inference('sup-', [status(thm)], ['42', '43'])).
% 4.59/4.79  thf('168', plain,
% 4.59/4.79      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.59/4.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.59/4.79      inference('sup+', [status(thm)], ['166', '167'])).
% 4.59/4.79  thf(t52_pre_topc, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( l1_pre_topc @ A ) =>
% 4.59/4.79       ( ![B:$i]:
% 4.59/4.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.59/4.79           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 4.59/4.79             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 4.59/4.79               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 4.59/4.79  thf('169', plain,
% 4.59/4.79      (![X48 : $i, X49 : $i]:
% 4.59/4.79         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 4.59/4.79          | ~ (v4_pre_topc @ X48 @ X49)
% 4.59/4.79          | ((k2_pre_topc @ X49 @ X48) = (X48))
% 4.59/4.79          | ~ (l1_pre_topc @ X49))),
% 4.59/4.79      inference('cnf', [status(esa)], [t52_pre_topc])).
% 4.59/4.79  thf('170', plain,
% 4.59/4.79      ((~ (l1_pre_topc @ sk_A)
% 4.59/4.79        | ((k2_pre_topc @ sk_A @ (k1_relat_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))
% 4.59/4.79        | ~ (v4_pre_topc @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 4.59/4.79      inference('sup-', [status(thm)], ['168', '169'])).
% 4.59/4.79  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('172', plain,
% 4.59/4.79      ((((k2_pre_topc @ sk_A @ (k1_relat_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))
% 4.59/4.79        | ~ (v4_pre_topc @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 4.59/4.79      inference('demod', [status(thm)], ['170', '171'])).
% 4.59/4.79  thf('173', plain,
% 4.59/4.79      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.59/4.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.59/4.79      inference('sup+', [status(thm)], ['166', '167'])).
% 4.59/4.79  thf(t18_tdlat_3, axiom,
% 4.59/4.79    (![A:$i]:
% 4.59/4.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.59/4.79       ( ( v1_tdlat_3 @ A ) <=>
% 4.59/4.79         ( ![B:$i]:
% 4.59/4.79           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.59/4.79             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 4.59/4.79  thf('174', plain,
% 4.59/4.79      (![X71 : $i, X72 : $i]:
% 4.59/4.79         (~ (v1_tdlat_3 @ X71)
% 4.59/4.79          | (v4_pre_topc @ X72 @ X71)
% 4.59/4.79          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (u1_struct_0 @ X71)))
% 4.59/4.79          | ~ (l1_pre_topc @ X71)
% 4.59/4.79          | ~ (v2_pre_topc @ X71))),
% 4.59/4.79      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 4.59/4.79  thf('175', plain,
% 4.59/4.79      ((~ (v2_pre_topc @ sk_A)
% 4.59/4.79        | ~ (l1_pre_topc @ sk_A)
% 4.59/4.79        | (v4_pre_topc @ (k1_relat_1 @ sk_C_1) @ sk_A)
% 4.59/4.79        | ~ (v1_tdlat_3 @ sk_A))),
% 4.59/4.79      inference('sup-', [status(thm)], ['173', '174'])).
% 4.59/4.79  thf('176', plain, ((v2_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('178', plain, ((v1_tdlat_3 @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('179', plain, ((v4_pre_topc @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 4.59/4.79      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 4.59/4.79  thf('180', plain,
% 4.59/4.79      (((k2_pre_topc @ sk_A @ (k1_relat_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))),
% 4.59/4.79      inference('demod', [status(thm)], ['172', '179'])).
% 4.59/4.79  thf('181', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['41', '56'])).
% 4.59/4.79  thf('182', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('demod', [status(thm)], ['139', '152'])).
% 4.59/4.79  thf('183', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['41', '56'])).
% 4.59/4.79  thf('184', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('demod', [status(thm)], ['139', '152'])).
% 4.59/4.79  thf('185', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 4.59/4.79  thf('186', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.59/4.79      inference('clc', [status(thm)], ['104', '107'])).
% 4.59/4.79  thf('187', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 4.59/4.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.59/4.79  thf('188', plain, ((v2_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('190', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['148', '149'])).
% 4.59/4.79  thf('191', plain, (![X44 : $i, X45 : $i]: (v1_funct_1 @ (sk_C @ X44 @ X45))),
% 4.59/4.79      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.59/4.79  thf('192', plain, ((v1_funct_1 @ k1_xboole_0)),
% 4.59/4.79      inference('sup+', [status(thm)], ['190', '191'])).
% 4.59/4.79  thf('193', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.59/4.79      inference('clc', [status(thm)], ['104', '107'])).
% 4.59/4.79  thf('194', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.59/4.79      inference('sup-', [status(thm)], ['148', '149'])).
% 4.59/4.79  thf('195', plain,
% 4.59/4.79      (![X44 : $i, X45 : $i]: (v1_funct_2 @ (sk_C @ X44 @ X45) @ X45 @ X44)),
% 4.59/4.79      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.59/4.79  thf('196', plain,
% 4.59/4.79      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.59/4.79      inference('sup+', [status(thm)], ['194', '195'])).
% 4.59/4.79  thf('197', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.59/4.79      inference('clc', [status(thm)], ['104', '107'])).
% 4.59/4.79  thf('198', plain,
% 4.59/4.79      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.79      inference('simplify', [status(thm)], ['5'])).
% 4.59/4.79  thf('199', plain,
% 4.59/4.79      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 4.59/4.79      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.59/4.79  thf('200', plain, ((l1_pre_topc @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('201', plain, ((v2_pre_topc @ sk_B_3)),
% 4.59/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.79  thf('202', plain, ((v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 4.59/4.79      inference('demod', [status(thm)],
% 4.59/4.79                ['115', '116', '117', '155', '185', '186', '187', '188', 
% 4.59/4.79                 '189', '192', '193', '196', '197', '198', '199', '200', '201'])).
% 4.59/4.79  thf('203', plain, ($false), inference('demod', [status(thm)], ['58', '202'])).
% 4.59/4.79  
% 4.59/4.79  % SZS output end Refutation
% 4.59/4.79  
% 4.59/4.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
