%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MqDE8Gr043

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:44 EST 2020

% Result     : Theorem 3.34s
% Output     : Refutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  263 (2992 expanded)
%              Number of leaves         :   66 ( 949 expanded)
%              Depth                    :   21
%              Number of atoms          : 1838 (42266 expanded)
%              Number of equality atoms :   87 ( 708 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( ( k2_struct_0 @ X44 )
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

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('10',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X41: $i] :
      ( ( l1_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X41: $i] :
      ( ( l1_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
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
    inference('sup-',[status(thm)],['9','28'])).

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
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( zip_tseitin_0 @ X55 @ X56 )
      | ( zip_tseitin_2 @ X57 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X56 ) @ ( u1_struct_0 @ X55 ) ) ) )
      | ~ ( v1_funct_2 @ X57 @ ( u1_struct_0 @ X56 ) @ ( u1_struct_0 @ X55 ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( l1_pre_topc @ X56 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
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
    ! [X63: $i,X64: $i] :
      ( ~ ( v1_tdlat_3 @ X63 )
      | ( v3_pre_topc @ X64 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X63 )
      | ~ ( v2_pre_topc @ X63 ) ) ),
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
    ! [X46: $i,X47: $i,X49: $i,X50: $i] :
      ( ( zip_tseitin_1 @ X46 @ X49 @ X47 @ X50 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X47 ) @ X49 @ X46 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X51 @ X52 @ X53 ) @ X53 @ X52 @ X51 )
      | ( v5_pre_topc @ X53 @ X51 @ X52 )
      | ~ ( zip_tseitin_2 @ X53 @ X52 @ X51 ) ) ),
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
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v2_pre_topc @ X58 )
      | ~ ( l1_pre_topc @ X58 )
      | ( m1_subset_1 @ ( sk_D_1 @ X59 @ X58 @ X60 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( v5_pre_topc @ X59 @ X60 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X58 ) ) ) )
      | ~ ( v1_funct_2 @ X59 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X58 ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( ( k2_struct_0 @ X44 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('77',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
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
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
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
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
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
    inference('sup-',[status(thm)],['20','21'])).

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
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('113',plain,
    ( k1_xboole_0
    = ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v2_pre_topc @ X58 )
      | ~ ( l1_pre_topc @ X58 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X60 @ ( k8_relset_1 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X58 ) @ X59 @ ( sk_D_1 @ X59 @ X58 @ X60 ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X58 ) @ X59 @ ( k2_pre_topc @ X58 @ ( sk_D_1 @ X59 @ X58 @ X60 ) ) ) )
      | ( v5_pre_topc @ X59 @ X60 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X58 ) ) ) )
      | ~ ( v1_funct_2 @ X59 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X58 ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 ) ) ),
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
    ( k1_xboole_0
    = ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('118',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('119',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('121',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k8_relset_1 @ X35 @ X36 @ X37 @ X36 )
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('124',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('127',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('128',plain,(
    ! [X38: $i,X39: $i] :
      ( m1_subset_1 @ ( sk_C @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('129',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('136',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X38: $i,X39: $i] :
      ( v4_relat_1 @ ( sk_C @ X38 @ X39 ) @ X39 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('138',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X38: $i,X39: $i] :
      ( v1_relat_1 @ ( sk_C @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['136','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('149',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('151',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( v1_tdlat_3 @ X65 )
      | ( v4_pre_topc @ X66 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X65 )
      | ~ ( v2_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

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

thf('158',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v4_pre_topc @ X42 @ X43 )
      | ( ( k2_pre_topc @ X43 @ X42 )
        = X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('165',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_pre_topc @ X43 )
      | ( ( k2_pre_topc @ X43 @ X42 )
       != X42 )
      | ( v4_pre_topc @ X42 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('169',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('174',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('177',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('179',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('183',plain,(
    ! [X38: $i,X39: $i] :
      ( v1_funct_1 @ ( sk_C @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('184',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('186',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('187',plain,(
    ! [X38: $i,X39: $i] :
      ( v1_funct_2 @ ( sk_C @ X38 @ X39 ) @ X39 @ X38 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('188',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['104','107'])).

thf('190',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('191',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('192',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ),
    inference(demod,[status(thm)],['115','116','117','146','177','178','179','180','181','184','185','188','189','190','191','192','193'])).

thf('195',plain,(
    $false ),
    inference(demod,[status(thm)],['58','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MqDE8Gr043
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.34/3.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.34/3.59  % Solved by: fo/fo7.sh
% 3.34/3.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.34/3.59  % done 4493 iterations in 3.136s
% 3.34/3.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.34/3.59  % SZS output start Refutation
% 3.34/3.59  thf(sk_B_type, type, sk_B: $i > $i).
% 3.34/3.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.34/3.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.34/3.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.34/3.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.34/3.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.34/3.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.34/3.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.34/3.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.34/3.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 3.34/3.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.34/3.59  thf(sk_A_type, type, sk_A: $i).
% 3.34/3.59  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 3.34/3.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.34/3.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.34/3.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.34/3.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.34/3.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 3.34/3.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.34/3.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.34/3.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.34/3.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.34/3.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 3.34/3.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.34/3.59  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 3.34/3.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.34/3.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.34/3.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.34/3.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.34/3.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.34/3.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.34/3.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.34/3.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.34/3.59  thf(sk_B_3_type, type, sk_B_3: $i).
% 3.34/3.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.34/3.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.34/3.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 3.34/3.59  thf(t68_tex_2, conjecture,
% 3.34/3.59    (![A:$i]:
% 3.34/3.59     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.34/3.59       ( ![B:$i]:
% 3.34/3.59         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 3.34/3.59           ( ![C:$i]:
% 3.34/3.59             ( ( ( v1_funct_1 @ C ) & 
% 3.34/3.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.34/3.59                 ( m1_subset_1 @
% 3.34/3.59                   C @ 
% 3.34/3.59                   ( k1_zfmisc_1 @
% 3.34/3.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.34/3.59               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 3.34/3.59  thf(zf_stmt_0, negated_conjecture,
% 3.34/3.59    (~( ![A:$i]:
% 3.34/3.59        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.34/3.59          ( ![B:$i]:
% 3.34/3.59            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 3.34/3.59              ( ![C:$i]:
% 3.34/3.59                ( ( ( v1_funct_1 @ C ) & 
% 3.34/3.59                    ( v1_funct_2 @
% 3.34/3.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.34/3.59                    ( m1_subset_1 @
% 3.34/3.59                      C @ 
% 3.34/3.59                      ( k1_zfmisc_1 @
% 3.34/3.59                        ( k2_zfmisc_1 @
% 3.34/3.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.34/3.59                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 3.34/3.59    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 3.34/3.59  thf('0', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf(t55_tops_2, axiom,
% 3.34/3.59    (![A:$i]:
% 3.34/3.59     ( ( l1_pre_topc @ A ) =>
% 3.34/3.59       ( ![B:$i]:
% 3.34/3.59         ( ( l1_pre_topc @ B ) =>
% 3.34/3.59           ( ![C:$i]:
% 3.34/3.59             ( ( ( m1_subset_1 @
% 3.34/3.59                   C @ 
% 3.34/3.59                   ( k1_zfmisc_1 @
% 3.34/3.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 3.34/3.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.34/3.59                 ( v1_funct_1 @ C ) ) =>
% 3.34/3.59               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 3.34/3.59                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.34/3.59                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.34/3.59                   ( ![D:$i]:
% 3.34/3.59                     ( ( m1_subset_1 @
% 3.34/3.59                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.34/3.59                       ( ( v3_pre_topc @ D @ B ) =>
% 3.34/3.59                         ( v3_pre_topc @
% 3.34/3.59                           ( k8_relset_1 @
% 3.34/3.59                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 3.34/3.59                           A ) ) ) ) ) ) ) ) ) ) ))).
% 3.34/3.59  thf(zf_stmt_1, axiom,
% 3.34/3.59    (![B:$i,A:$i]:
% 3.34/3.59     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 3.34/3.59         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.34/3.59       ( zip_tseitin_0 @ B @ A ) ))).
% 3.34/3.59  thf('1', plain,
% 3.34/3.59      (![X44 : $i, X45 : $i]:
% 3.34/3.59         ((zip_tseitin_0 @ X44 @ X45) | ((k2_struct_0 @ X44) = (k1_xboole_0)))),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.34/3.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.34/3.59  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.59  thf('3', plain,
% 3.34/3.59      (![X0 : $i, X1 : $i]:
% 3.34/3.59         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 3.34/3.59      inference('sup+', [status(thm)], ['1', '2'])).
% 3.34/3.59  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.59  thf(t8_boole, axiom,
% 3.34/3.59    (![A:$i,B:$i]:
% 3.34/3.59     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.34/3.59  thf('5', plain,
% 3.34/3.59      (![X8 : $i, X9 : $i]:
% 3.34/3.59         (~ (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X9) | ((X8) = (X9)))),
% 3.34/3.59      inference('cnf', [status(esa)], [t8_boole])).
% 3.34/3.59  thf('6', plain,
% 3.34/3.59      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.59      inference('sup-', [status(thm)], ['4', '5'])).
% 3.34/3.59  thf(t113_zfmisc_1, axiom,
% 3.34/3.59    (![A:$i,B:$i]:
% 3.34/3.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.34/3.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.34/3.59  thf('7', plain,
% 3.34/3.59      (![X11 : $i, X12 : $i]:
% 3.34/3.59         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 3.34/3.59          | ((X12) != (k1_xboole_0)))),
% 3.34/3.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.34/3.59  thf('8', plain,
% 3.34/3.59      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.59      inference('simplify', [status(thm)], ['7'])).
% 3.34/3.59  thf('9', plain,
% 3.34/3.59      (![X0 : $i, X1 : $i]:
% 3.34/3.59         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.59      inference('sup+', [status(thm)], ['6', '8'])).
% 3.34/3.59  thf(d3_struct_0, axiom,
% 3.34/3.59    (![A:$i]:
% 3.34/3.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.34/3.59  thf('10', plain,
% 3.34/3.59      (![X40 : $i]:
% 3.34/3.59         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 3.34/3.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.34/3.59  thf('11', plain,
% 3.34/3.59      (![X40 : $i]:
% 3.34/3.59         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 3.34/3.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.34/3.59  thf('12', plain,
% 3.34/3.59      ((m1_subset_1 @ sk_C_1 @ 
% 3.34/3.59        (k1_zfmisc_1 @ 
% 3.34/3.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf(t3_subset, axiom,
% 3.34/3.59    (![A:$i,B:$i]:
% 3.34/3.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.34/3.59  thf('13', plain,
% 3.34/3.59      (![X15 : $i, X16 : $i]:
% 3.34/3.59         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 3.34/3.59      inference('cnf', [status(esa)], [t3_subset])).
% 3.34/3.59  thf('14', plain,
% 3.34/3.59      ((r1_tarski @ sk_C_1 @ 
% 3.34/3.59        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))),
% 3.34/3.59      inference('sup-', [status(thm)], ['12', '13'])).
% 3.34/3.59  thf('15', plain,
% 3.34/3.59      (((r1_tarski @ sk_C_1 @ 
% 3.34/3.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))
% 3.34/3.59        | ~ (l1_struct_0 @ sk_A))),
% 3.34/3.59      inference('sup+', [status(thm)], ['11', '14'])).
% 3.34/3.59  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf(dt_l1_pre_topc, axiom,
% 3.34/3.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.34/3.59  thf('17', plain,
% 3.34/3.59      (![X41 : $i]: ((l1_struct_0 @ X41) | ~ (l1_pre_topc @ X41))),
% 3.34/3.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.34/3.59  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 3.34/3.59      inference('sup-', [status(thm)], ['16', '17'])).
% 3.34/3.59  thf('19', plain,
% 3.34/3.59      ((r1_tarski @ sk_C_1 @ 
% 3.34/3.59        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))),
% 3.34/3.59      inference('demod', [status(thm)], ['15', '18'])).
% 3.34/3.59  thf('20', plain,
% 3.34/3.59      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.59      inference('sup-', [status(thm)], ['4', '5'])).
% 3.34/3.59  thf(t3_xboole_1, axiom,
% 3.34/3.59    (![A:$i]:
% 3.34/3.59     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.34/3.59  thf('21', plain,
% 3.34/3.59      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 3.34/3.59      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.34/3.59  thf('22', plain,
% 3.34/3.59      (![X0 : $i, X1 : $i]:
% 3.34/3.59         (~ (r1_tarski @ X1 @ X0)
% 3.34/3.59          | ~ (v1_xboole_0 @ X0)
% 3.34/3.59          | ((X1) = (k1_xboole_0)))),
% 3.34/3.59      inference('sup-', [status(thm)], ['20', '21'])).
% 3.34/3.59  thf('23', plain,
% 3.34/3.59      ((((sk_C_1) = (k1_xboole_0))
% 3.34/3.59        | ~ (v1_xboole_0 @ 
% 3.34/3.59             (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 3.34/3.59      inference('sup-', [status(thm)], ['19', '22'])).
% 3.34/3.59  thf('24', plain,
% 3.34/3.59      ((~ (v1_xboole_0 @ 
% 3.34/3.59           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_3)))
% 3.34/3.59        | ~ (l1_struct_0 @ sk_B_3)
% 3.34/3.59        | ((sk_C_1) = (k1_xboole_0)))),
% 3.34/3.59      inference('sup-', [status(thm)], ['10', '23'])).
% 3.34/3.59  thf('25', plain, ((l1_pre_topc @ sk_B_3)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('26', plain,
% 3.34/3.59      (![X41 : $i]: ((l1_struct_0 @ X41) | ~ (l1_pre_topc @ X41))),
% 3.34/3.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.34/3.59  thf('27', plain, ((l1_struct_0 @ sk_B_3)),
% 3.34/3.59      inference('sup-', [status(thm)], ['25', '26'])).
% 3.34/3.59  thf('28', plain,
% 3.34/3.59      ((~ (v1_xboole_0 @ 
% 3.34/3.59           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_3)))
% 3.34/3.59        | ((sk_C_1) = (k1_xboole_0)))),
% 3.34/3.59      inference('demod', [status(thm)], ['24', '27'])).
% 3.34/3.59  thf('29', plain,
% 3.34/3.59      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.34/3.59        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 3.34/3.59        | ((sk_C_1) = (k1_xboole_0)))),
% 3.34/3.59      inference('sup-', [status(thm)], ['9', '28'])).
% 3.34/3.59  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.59  thf('31', plain,
% 3.34/3.59      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3)) | ((sk_C_1) = (k1_xboole_0)))),
% 3.34/3.59      inference('demod', [status(thm)], ['29', '30'])).
% 3.34/3.59  thf('32', plain,
% 3.34/3.59      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_3 @ X0) | ((sk_C_1) = (k1_xboole_0)))),
% 3.34/3.59      inference('sup-', [status(thm)], ['3', '31'])).
% 3.34/3.59  thf('33', plain,
% 3.34/3.59      ((m1_subset_1 @ sk_C_1 @ 
% 3.34/3.59        (k1_zfmisc_1 @ 
% 3.34/3.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 3.34/3.59  thf(zf_stmt_3, axiom,
% 3.34/3.59    (![C:$i,B:$i,A:$i]:
% 3.34/3.59     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 3.34/3.59       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.34/3.59         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 3.34/3.59  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 3.34/3.59  thf(zf_stmt_5, axiom,
% 3.34/3.59    (![D:$i,C:$i,B:$i,A:$i]:
% 3.34/3.59     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 3.34/3.59       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.34/3.59         ( ( v3_pre_topc @ D @ B ) =>
% 3.34/3.59           ( v3_pre_topc @
% 3.34/3.59             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 3.34/3.59             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 3.34/3.59  thf(zf_stmt_7, axiom,
% 3.34/3.59    (![A:$i]:
% 3.34/3.59     ( ( l1_pre_topc @ A ) =>
% 3.34/3.59       ( ![B:$i]:
% 3.34/3.59         ( ( l1_pre_topc @ B ) =>
% 3.34/3.59           ( ![C:$i]:
% 3.34/3.59             ( ( ( v1_funct_1 @ C ) & 
% 3.34/3.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.34/3.59                 ( m1_subset_1 @
% 3.34/3.59                   C @ 
% 3.34/3.59                   ( k1_zfmisc_1 @
% 3.34/3.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.34/3.59               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 3.34/3.59  thf('34', plain,
% 3.34/3.59      (![X55 : $i, X56 : $i, X57 : $i]:
% 3.34/3.59         (~ (l1_pre_topc @ X55)
% 3.34/3.59          | ~ (zip_tseitin_0 @ X55 @ X56)
% 3.34/3.59          | (zip_tseitin_2 @ X57 @ X55 @ X56)
% 3.34/3.59          | ~ (m1_subset_1 @ X57 @ 
% 3.34/3.59               (k1_zfmisc_1 @ 
% 3.34/3.59                (k2_zfmisc_1 @ (u1_struct_0 @ X56) @ (u1_struct_0 @ X55))))
% 3.34/3.59          | ~ (v1_funct_2 @ X57 @ (u1_struct_0 @ X56) @ (u1_struct_0 @ X55))
% 3.34/3.59          | ~ (v1_funct_1 @ X57)
% 3.34/3.59          | ~ (l1_pre_topc @ X56))),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.34/3.59  thf('35', plain,
% 3.34/3.59      ((~ (l1_pre_topc @ sk_A)
% 3.34/3.59        | ~ (v1_funct_1 @ sk_C_1)
% 3.34/3.59        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 3.34/3.59             (u1_struct_0 @ sk_B_3))
% 3.34/3.59        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 3.34/3.59        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A)
% 3.34/3.59        | ~ (l1_pre_topc @ sk_B_3))),
% 3.34/3.59      inference('sup-', [status(thm)], ['33', '34'])).
% 3.34/3.59  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('38', plain,
% 3.34/3.59      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('39', plain, ((l1_pre_topc @ sk_B_3)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('40', plain,
% 3.34/3.59      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 3.34/3.59        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 3.34/3.59      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 3.34/3.59  thf('41', plain,
% 3.34/3.59      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 3.34/3.59      inference('sup-', [status(thm)], ['32', '40'])).
% 3.34/3.59  thf('42', plain,
% 3.34/3.59      ((m1_subset_1 @ sk_C_1 @ 
% 3.34/3.59        (k1_zfmisc_1 @ 
% 3.34/3.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf(dt_k8_relset_1, axiom,
% 3.34/3.59    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.59       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.34/3.59  thf('43', plain,
% 3.34/3.59      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.34/3.59         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.34/3.59          | (m1_subset_1 @ (k8_relset_1 @ X29 @ X30 @ X28 @ X31) @ 
% 3.34/3.59             (k1_zfmisc_1 @ X29)))),
% 3.34/3.59      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 3.34/3.59  thf('44', plain,
% 3.34/3.59      (![X0 : $i]:
% 3.34/3.59         (m1_subset_1 @ 
% 3.34/3.59          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 3.34/3.59           sk_C_1 @ X0) @ 
% 3.34/3.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.34/3.59      inference('sup-', [status(thm)], ['42', '43'])).
% 3.34/3.59  thf(t17_tdlat_3, axiom,
% 3.34/3.59    (![A:$i]:
% 3.34/3.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.34/3.59       ( ( v1_tdlat_3 @ A ) <=>
% 3.34/3.59         ( ![B:$i]:
% 3.34/3.59           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.34/3.59             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 3.34/3.59  thf('45', plain,
% 3.34/3.59      (![X63 : $i, X64 : $i]:
% 3.34/3.59         (~ (v1_tdlat_3 @ X63)
% 3.34/3.59          | (v3_pre_topc @ X64 @ X63)
% 3.34/3.59          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 3.34/3.59          | ~ (l1_pre_topc @ X63)
% 3.34/3.59          | ~ (v2_pre_topc @ X63))),
% 3.34/3.59      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 3.34/3.59  thf('46', plain,
% 3.34/3.59      (![X0 : $i]:
% 3.34/3.59         (~ (v2_pre_topc @ sk_A)
% 3.34/3.59          | ~ (l1_pre_topc @ sk_A)
% 3.34/3.59          | (v3_pre_topc @ 
% 3.34/3.59             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 3.34/3.59              sk_C_1 @ X0) @ 
% 3.34/3.59             sk_A)
% 3.34/3.59          | ~ (v1_tdlat_3 @ sk_A))),
% 3.34/3.59      inference('sup-', [status(thm)], ['44', '45'])).
% 3.34/3.59  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('49', plain, ((v1_tdlat_3 @ sk_A)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('50', plain,
% 3.34/3.59      (![X0 : $i]:
% 3.34/3.59         (v3_pre_topc @ 
% 3.34/3.59          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 3.34/3.59           sk_C_1 @ X0) @ 
% 3.34/3.59          sk_A)),
% 3.34/3.59      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 3.34/3.59  thf('51', plain,
% 3.34/3.59      (![X46 : $i, X47 : $i, X49 : $i, X50 : $i]:
% 3.34/3.59         ((zip_tseitin_1 @ X46 @ X49 @ X47 @ X50)
% 3.34/3.59          | ~ (v3_pre_topc @ 
% 3.34/3.59               (k8_relset_1 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X47) @ 
% 3.34/3.59                X49 @ X46) @ 
% 3.34/3.59               X50))),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.34/3.59  thf('52', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 3.34/3.59      inference('sup-', [status(thm)], ['50', '51'])).
% 3.34/3.59  thf('53', plain,
% 3.34/3.59      (![X51 : $i, X52 : $i, X53 : $i]:
% 3.34/3.59         (~ (zip_tseitin_1 @ (sk_D @ X51 @ X52 @ X53) @ X53 @ X52 @ X51)
% 3.34/3.59          | (v5_pre_topc @ X53 @ X51 @ X52)
% 3.34/3.59          | ~ (zip_tseitin_2 @ X53 @ X52 @ X51))),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.34/3.59  thf('54', plain,
% 3.34/3.59      ((~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 3.34/3.59        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3))),
% 3.34/3.59      inference('sup-', [status(thm)], ['52', '53'])).
% 3.34/3.59  thf('55', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 3.34/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.59  thf('56', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 3.34/3.59      inference('clc', [status(thm)], ['54', '55'])).
% 3.34/3.59  thf('57', plain, (((sk_C_1) = (k1_xboole_0))),
% 3.34/3.59      inference('sup-', [status(thm)], ['41', '56'])).
% 3.34/3.59  thf('58', plain, (~ (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 3.34/3.59      inference('demod', [status(thm)], ['0', '57'])).
% 3.34/3.59  thf(d1_xboole_0, axiom,
% 3.34/3.59    (![A:$i]:
% 3.34/3.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.34/3.59  thf('59', plain,
% 3.34/3.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.34/3.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.60  thf('60', plain,
% 3.34/3.60      ((m1_subset_1 @ sk_C_1 @ 
% 3.34/3.60        (k1_zfmisc_1 @ 
% 3.34/3.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf(t56_tops_2, axiom,
% 3.34/3.60    (![A:$i]:
% 3.34/3.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.34/3.60       ( ![B:$i]:
% 3.34/3.60         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 3.34/3.60           ( ![C:$i]:
% 3.34/3.60             ( ( ( v1_funct_1 @ C ) & 
% 3.34/3.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.34/3.60                 ( m1_subset_1 @
% 3.34/3.60                   C @ 
% 3.34/3.60                   ( k1_zfmisc_1 @
% 3.34/3.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.34/3.60               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.34/3.60                 ( ![D:$i]:
% 3.34/3.60                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.34/3.60                     ( r1_tarski @
% 3.34/3.60                       ( k2_pre_topc @
% 3.34/3.60                         A @ 
% 3.34/3.60                         ( k8_relset_1 @
% 3.34/3.60                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 3.34/3.60                       ( k8_relset_1 @
% 3.34/3.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 3.34/3.60                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.34/3.60  thf('61', plain,
% 3.34/3.60      (![X58 : $i, X59 : $i, X60 : $i]:
% 3.34/3.60         (~ (v2_pre_topc @ X58)
% 3.34/3.60          | ~ (l1_pre_topc @ X58)
% 3.34/3.60          | (m1_subset_1 @ (sk_D_1 @ X59 @ X58 @ X60) @ 
% 3.34/3.60             (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 3.34/3.60          | (v5_pre_topc @ X59 @ X60 @ X58)
% 3.34/3.60          | ~ (m1_subset_1 @ X59 @ 
% 3.34/3.60               (k1_zfmisc_1 @ 
% 3.34/3.60                (k2_zfmisc_1 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X58))))
% 3.34/3.60          | ~ (v1_funct_2 @ X59 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X58))
% 3.34/3.60          | ~ (v1_funct_1 @ X59)
% 3.34/3.60          | ~ (l1_pre_topc @ X60)
% 3.34/3.60          | ~ (v2_pre_topc @ X60))),
% 3.34/3.60      inference('cnf', [status(esa)], [t56_tops_2])).
% 3.34/3.60  thf('62', plain,
% 3.34/3.60      ((~ (v2_pre_topc @ sk_A)
% 3.34/3.60        | ~ (l1_pre_topc @ sk_A)
% 3.34/3.60        | ~ (v1_funct_1 @ sk_C_1)
% 3.34/3.60        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 3.34/3.60             (u1_struct_0 @ sk_B_3))
% 3.34/3.60        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)
% 3.34/3.60        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 3.34/3.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))
% 3.34/3.60        | ~ (l1_pre_topc @ sk_B_3)
% 3.34/3.60        | ~ (v2_pre_topc @ sk_B_3))),
% 3.34/3.60      inference('sup-', [status(thm)], ['60', '61'])).
% 3.34/3.60  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('65', plain, ((v1_funct_1 @ sk_C_1)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('66', plain,
% 3.34/3.60      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('67', plain, ((l1_pre_topc @ sk_B_3)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('68', plain, ((v2_pre_topc @ sk_B_3)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('69', plain,
% 3.34/3.60      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)
% 3.34/3.60        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 3.34/3.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3))))),
% 3.34/3.60      inference('demod', [status(thm)],
% 3.34/3.60                ['62', '63', '64', '65', '66', '67', '68'])).
% 3.34/3.60  thf('70', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('71', plain,
% 3.34/3.60      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 3.34/3.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 3.34/3.60      inference('clc', [status(thm)], ['69', '70'])).
% 3.34/3.60  thf(t5_subset, axiom,
% 3.34/3.60    (![A:$i,B:$i,C:$i]:
% 3.34/3.60     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.34/3.60          ( v1_xboole_0 @ C ) ) ))).
% 3.34/3.60  thf('72', plain,
% 3.34/3.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.34/3.60         (~ (r2_hidden @ X18 @ X19)
% 3.34/3.60          | ~ (v1_xboole_0 @ X20)
% 3.34/3.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 3.34/3.60      inference('cnf', [status(esa)], [t5_subset])).
% 3.34/3.60  thf('73', plain,
% 3.34/3.60      (![X0 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 3.34/3.60          | ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 3.34/3.60      inference('sup-', [status(thm)], ['71', '72'])).
% 3.34/3.60  thf('74', plain, (((sk_C_1) = (k1_xboole_0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['41', '56'])).
% 3.34/3.60  thf('75', plain,
% 3.34/3.60      (![X0 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 3.34/3.60          | ~ (r2_hidden @ X0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A)))),
% 3.34/3.60      inference('demod', [status(thm)], ['73', '74'])).
% 3.34/3.60  thf('76', plain,
% 3.34/3.60      (![X44 : $i, X45 : $i]:
% 3.34/3.60         ((zip_tseitin_0 @ X44 @ X45) | ((k2_struct_0 @ X44) = (k1_xboole_0)))),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.34/3.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.34/3.60  thf('77', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 3.34/3.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.34/3.60  thf('78', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.60         ((r1_tarski @ (k2_struct_0 @ X0) @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 3.34/3.60      inference('sup+', [status(thm)], ['76', '77'])).
% 3.34/3.60  thf('79', plain,
% 3.34/3.60      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 3.34/3.60        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 3.34/3.60  thf('80', plain,
% 3.34/3.60      (![X0 : $i]:
% 3.34/3.60         ((r1_tarski @ (k2_struct_0 @ sk_B_3) @ X0)
% 3.34/3.60          | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('sup-', [status(thm)], ['78', '79'])).
% 3.34/3.60  thf('81', plain,
% 3.34/3.60      (![X40 : $i]:
% 3.34/3.60         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 3.34/3.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.34/3.60  thf('82', plain,
% 3.34/3.60      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 3.34/3.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 3.34/3.60      inference('clc', [status(thm)], ['69', '70'])).
% 3.34/3.60  thf('83', plain,
% 3.34/3.60      (![X15 : $i, X16 : $i]:
% 3.34/3.60         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 3.34/3.60      inference('cnf', [status(esa)], [t3_subset])).
% 3.34/3.60  thf('84', plain,
% 3.34/3.60      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 3.34/3.60      inference('sup-', [status(thm)], ['82', '83'])).
% 3.34/3.60  thf(d10_xboole_0, axiom,
% 3.34/3.60    (![A:$i,B:$i]:
% 3.34/3.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.34/3.60  thf('85', plain,
% 3.34/3.60      (![X3 : $i, X5 : $i]:
% 3.34/3.60         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 3.34/3.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.34/3.60  thf('86', plain,
% 3.34/3.60      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_3) @ 
% 3.34/3.60           (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A))
% 3.34/3.60        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 3.34/3.60      inference('sup-', [status(thm)], ['84', '85'])).
% 3.34/3.60  thf('87', plain,
% 3.34/3.60      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_3) @ 
% 3.34/3.60           (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A))
% 3.34/3.60        | ~ (l1_struct_0 @ sk_B_3)
% 3.34/3.60        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 3.34/3.60      inference('sup-', [status(thm)], ['81', '86'])).
% 3.34/3.60  thf('88', plain, ((l1_struct_0 @ sk_B_3)),
% 3.34/3.60      inference('sup-', [status(thm)], ['25', '26'])).
% 3.34/3.60  thf('89', plain,
% 3.34/3.60      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_3) @ 
% 3.34/3.60           (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A))
% 3.34/3.60        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 3.34/3.60      inference('demod', [status(thm)], ['87', '88'])).
% 3.34/3.60  thf('90', plain,
% 3.34/3.60      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 3.34/3.60        | ((u1_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 3.34/3.60      inference('sup-', [status(thm)], ['80', '89'])).
% 3.34/3.60  thf('91', plain,
% 3.34/3.60      (![X40 : $i]:
% 3.34/3.60         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 3.34/3.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.34/3.60  thf('92', plain,
% 3.34/3.60      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 3.34/3.60      inference('sup-', [status(thm)], ['82', '83'])).
% 3.34/3.60  thf('93', plain,
% 3.34/3.60      (((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (k2_struct_0 @ sk_B_3))
% 3.34/3.60        | ~ (l1_struct_0 @ sk_B_3))),
% 3.34/3.60      inference('sup+', [status(thm)], ['91', '92'])).
% 3.34/3.60  thf('94', plain, ((l1_struct_0 @ sk_B_3)),
% 3.34/3.60      inference('sup-', [status(thm)], ['25', '26'])).
% 3.34/3.60  thf('95', plain,
% 3.34/3.60      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (k2_struct_0 @ sk_B_3))),
% 3.34/3.60      inference('demod', [status(thm)], ['93', '94'])).
% 3.34/3.60  thf('96', plain,
% 3.34/3.60      (((r1_tarski @ (u1_struct_0 @ sk_B_3) @ (k2_struct_0 @ sk_B_3))
% 3.34/3.60        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('sup+', [status(thm)], ['90', '95'])).
% 3.34/3.60  thf('97', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         (~ (r1_tarski @ X1 @ X0)
% 3.34/3.60          | ~ (v1_xboole_0 @ X0)
% 3.34/3.60          | ((X1) = (k1_xboole_0)))),
% 3.34/3.60      inference('sup-', [status(thm)], ['20', '21'])).
% 3.34/3.60  thf('98', plain,
% 3.34/3.60      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 3.34/3.60        | ((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 3.34/3.60        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3)))),
% 3.34/3.60      inference('sup-', [status(thm)], ['96', '97'])).
% 3.34/3.60  thf('99', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 3.34/3.60      inference('sup+', [status(thm)], ['1', '2'])).
% 3.34/3.60  thf('100', plain,
% 3.34/3.60      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 3.34/3.60        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 3.34/3.60  thf('101', plain,
% 3.34/3.60      (((v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 3.34/3.60        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('sup-', [status(thm)], ['99', '100'])).
% 3.34/3.60  thf('102', plain,
% 3.34/3.60      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 3.34/3.60        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('clc', [status(thm)], ['98', '101'])).
% 3.34/3.60  thf('103', plain, (((sk_C_1) = (k1_xboole_0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['41', '56'])).
% 3.34/3.60  thf('104', plain,
% 3.34/3.60      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 3.34/3.60        | (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('demod', [status(thm)], ['102', '103'])).
% 3.34/3.60  thf('105', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 3.34/3.60      inference('clc', [status(thm)], ['54', '55'])).
% 3.34/3.60  thf('106', plain, (((sk_C_1) = (k1_xboole_0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['41', '56'])).
% 3.34/3.60  thf('107', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)),
% 3.34/3.60      inference('demod', [status(thm)], ['105', '106'])).
% 3.34/3.60  thf('108', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 3.34/3.60      inference('clc', [status(thm)], ['104', '107'])).
% 3.34/3.60  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.60  thf('110', plain,
% 3.34/3.60      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('demod', [status(thm)], ['75', '108', '109'])).
% 3.34/3.60  thf('111', plain, ((v1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('sup-', [status(thm)], ['59', '110'])).
% 3.34/3.60  thf('112', plain,
% 3.34/3.60      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['4', '5'])).
% 3.34/3.60  thf('113', plain, (((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('sup-', [status(thm)], ['111', '112'])).
% 3.34/3.60  thf('114', plain,
% 3.34/3.60      (![X58 : $i, X59 : $i, X60 : $i]:
% 3.34/3.60         (~ (v2_pre_topc @ X58)
% 3.34/3.60          | ~ (l1_pre_topc @ X58)
% 3.34/3.60          | ~ (r1_tarski @ 
% 3.34/3.60               (k2_pre_topc @ X60 @ 
% 3.34/3.60                (k8_relset_1 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X58) @ 
% 3.34/3.60                 X59 @ (sk_D_1 @ X59 @ X58 @ X60))) @ 
% 3.34/3.60               (k8_relset_1 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X58) @ 
% 3.34/3.60                X59 @ (k2_pre_topc @ X58 @ (sk_D_1 @ X59 @ X58 @ X60))))
% 3.34/3.60          | (v5_pre_topc @ X59 @ X60 @ X58)
% 3.34/3.60          | ~ (m1_subset_1 @ X59 @ 
% 3.34/3.60               (k1_zfmisc_1 @ 
% 3.34/3.60                (k2_zfmisc_1 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X58))))
% 3.34/3.60          | ~ (v1_funct_2 @ X59 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X58))
% 3.34/3.60          | ~ (v1_funct_1 @ X59)
% 3.34/3.60          | ~ (l1_pre_topc @ X60)
% 3.34/3.60          | ~ (v2_pre_topc @ X60))),
% 3.34/3.60      inference('cnf', [status(esa)], [t56_tops_2])).
% 3.34/3.60  thf('115', plain,
% 3.34/3.60      ((~ (r1_tarski @ 
% 3.34/3.60           (k2_pre_topc @ sk_A @ 
% 3.34/3.60            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 3.34/3.60             k1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))) @ 
% 3.34/3.60           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 3.34/3.60            k1_xboole_0 @ (k2_pre_topc @ sk_B_3 @ k1_xboole_0)))
% 3.34/3.60        | ~ (v2_pre_topc @ sk_A)
% 3.34/3.60        | ~ (l1_pre_topc @ sk_A)
% 3.34/3.60        | ~ (v1_funct_1 @ k1_xboole_0)
% 3.34/3.60        | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.34/3.60             (u1_struct_0 @ sk_B_3))
% 3.34/3.60        | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 3.34/3.60             (k1_zfmisc_1 @ 
% 3.34/3.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))
% 3.34/3.60        | (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)
% 3.34/3.60        | ~ (l1_pre_topc @ sk_B_3)
% 3.34/3.60        | ~ (v2_pre_topc @ sk_B_3))),
% 3.34/3.60      inference('sup-', [status(thm)], ['113', '114'])).
% 3.34/3.60  thf('116', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 3.34/3.60      inference('clc', [status(thm)], ['104', '107'])).
% 3.34/3.60  thf('117', plain, (((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 3.34/3.60      inference('sup-', [status(thm)], ['111', '112'])).
% 3.34/3.60  thf('118', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 3.34/3.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.34/3.60  thf('119', plain,
% 3.34/3.60      (![X15 : $i, X17 : $i]:
% 3.34/3.60         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 3.34/3.60      inference('cnf', [status(esa)], [t3_subset])).
% 3.34/3.60  thf('120', plain,
% 3.34/3.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['118', '119'])).
% 3.34/3.60  thf(t38_relset_1, axiom,
% 3.34/3.60    (![A:$i,B:$i,C:$i]:
% 3.34/3.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.60       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 3.34/3.60         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.34/3.60  thf('121', plain,
% 3.34/3.60      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.34/3.60         (((k8_relset_1 @ X35 @ X36 @ X37 @ X36)
% 3.34/3.60            = (k1_relset_1 @ X35 @ X36 @ X37))
% 3.34/3.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 3.34/3.60      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.34/3.60  thf('122', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 3.34/3.60           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['120', '121'])).
% 3.34/3.60  thf('123', plain,
% 3.34/3.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['118', '119'])).
% 3.34/3.60  thf(redefinition_k1_relset_1, axiom,
% 3.34/3.60    (![A:$i,B:$i,C:$i]:
% 3.34/3.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.34/3.60  thf('124', plain,
% 3.34/3.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.34/3.60         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 3.34/3.60          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 3.34/3.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.34/3.60  thf('125', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['123', '124'])).
% 3.34/3.60  thf('126', plain,
% 3.34/3.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.34/3.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.60  thf('127', plain,
% 3.34/3.60      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.60      inference('simplify', [status(thm)], ['7'])).
% 3.34/3.60  thf(rc1_funct_2, axiom,
% 3.34/3.60    (![A:$i,B:$i]:
% 3.34/3.60     ( ?[C:$i]:
% 3.34/3.60       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 3.34/3.60         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 3.34/3.60         ( v1_relat_1 @ C ) & 
% 3.34/3.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.34/3.60  thf('128', plain,
% 3.34/3.60      (![X38 : $i, X39 : $i]:
% 3.34/3.60         (m1_subset_1 @ (sk_C @ X38 @ X39) @ 
% 3.34/3.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))),
% 3.34/3.60      inference('cnf', [status(esa)], [rc1_funct_2])).
% 3.34/3.60  thf('129', plain,
% 3.34/3.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.34/3.60         (~ (r2_hidden @ X18 @ X19)
% 3.34/3.60          | ~ (v1_xboole_0 @ X20)
% 3.34/3.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 3.34/3.60      inference('cnf', [status(esa)], [t5_subset])).
% 3.34/3.60  thf('130', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.34/3.60          | ~ (r2_hidden @ X2 @ (sk_C @ X0 @ X1)))),
% 3.34/3.60      inference('sup-', [status(thm)], ['128', '129'])).
% 3.34/3.60  thf('131', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.34/3.60          | ~ (r2_hidden @ X1 @ (sk_C @ k1_xboole_0 @ X0)))),
% 3.34/3.60      inference('sup-', [status(thm)], ['127', '130'])).
% 3.34/3.60  thf('132', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.60  thf('133', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (sk_C @ k1_xboole_0 @ X0))),
% 3.34/3.60      inference('demod', [status(thm)], ['131', '132'])).
% 3.34/3.60  thf('134', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['126', '133'])).
% 3.34/3.60  thf('135', plain,
% 3.34/3.60      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['4', '5'])).
% 3.34/3.60  thf('136', plain, (![X0 : $i]: ((k1_xboole_0) = (sk_C @ k1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['134', '135'])).
% 3.34/3.60  thf('137', plain,
% 3.34/3.60      (![X38 : $i, X39 : $i]: (v4_relat_1 @ (sk_C @ X38 @ X39) @ X39)),
% 3.34/3.60      inference('cnf', [status(esa)], [rc1_funct_2])).
% 3.34/3.60  thf(d18_relat_1, axiom,
% 3.34/3.60    (![A:$i,B:$i]:
% 3.34/3.60     ( ( v1_relat_1 @ B ) =>
% 3.34/3.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.34/3.60  thf('138', plain,
% 3.34/3.60      (![X21 : $i, X22 : $i]:
% 3.34/3.60         (~ (v4_relat_1 @ X21 @ X22)
% 3.34/3.60          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 3.34/3.60          | ~ (v1_relat_1 @ X21))),
% 3.34/3.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.34/3.60  thf('139', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         (~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 3.34/3.60          | (r1_tarski @ (k1_relat_1 @ (sk_C @ X1 @ X0)) @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['137', '138'])).
% 3.34/3.60  thf('140', plain, (![X38 : $i, X39 : $i]: (v1_relat_1 @ (sk_C @ X38 @ X39))),
% 3.34/3.60      inference('cnf', [status(esa)], [rc1_funct_2])).
% 3.34/3.60  thf('141', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k1_relat_1 @ (sk_C @ X1 @ X0)) @ X0)),
% 3.34/3.60      inference('demod', [status(thm)], ['139', '140'])).
% 3.34/3.60  thf('142', plain,
% 3.34/3.60      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 3.34/3.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.34/3.60  thf('143', plain,
% 3.34/3.60      (![X0 : $i]: ((k1_relat_1 @ (sk_C @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['141', '142'])).
% 3.34/3.60  thf('144', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.60      inference('sup+', [status(thm)], ['136', '143'])).
% 3.34/3.60  thf('145', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.60      inference('demod', [status(thm)], ['125', '144'])).
% 3.34/3.60  thf('146', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.34/3.60      inference('demod', [status(thm)], ['122', '145'])).
% 3.34/3.60  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('148', plain,
% 3.34/3.60      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['4', '5'])).
% 3.34/3.60  thf('149', plain,
% 3.34/3.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['118', '119'])).
% 3.34/3.60  thf('150', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup+', [status(thm)], ['148', '149'])).
% 3.34/3.60  thf(t18_tdlat_3, axiom,
% 3.34/3.60    (![A:$i]:
% 3.34/3.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.34/3.60       ( ( v1_tdlat_3 @ A ) <=>
% 3.34/3.60         ( ![B:$i]:
% 3.34/3.60           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.34/3.60             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 3.34/3.60  thf('151', plain,
% 3.34/3.60      (![X65 : $i, X66 : $i]:
% 3.34/3.60         (~ (v1_tdlat_3 @ X65)
% 3.34/3.60          | (v4_pre_topc @ X66 @ X65)
% 3.34/3.60          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 3.34/3.60          | ~ (l1_pre_topc @ X65)
% 3.34/3.60          | ~ (v2_pre_topc @ X65))),
% 3.34/3.60      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 3.34/3.60  thf('152', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ X1)
% 3.34/3.60          | ~ (v2_pre_topc @ X0)
% 3.34/3.60          | ~ (l1_pre_topc @ X0)
% 3.34/3.60          | (v4_pre_topc @ X1 @ X0)
% 3.34/3.60          | ~ (v1_tdlat_3 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['150', '151'])).
% 3.34/3.60  thf('153', plain,
% 3.34/3.60      (![X0 : $i]:
% 3.34/3.60         (~ (v1_tdlat_3 @ sk_A)
% 3.34/3.60          | (v4_pre_topc @ X0 @ sk_A)
% 3.34/3.60          | ~ (v2_pre_topc @ sk_A)
% 3.34/3.60          | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['147', '152'])).
% 3.34/3.60  thf('154', plain, ((v1_tdlat_3 @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('156', plain,
% 3.34/3.60      (![X0 : $i]: ((v4_pre_topc @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('demod', [status(thm)], ['153', '154', '155'])).
% 3.34/3.60  thf('157', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup+', [status(thm)], ['148', '149'])).
% 3.34/3.60  thf(t52_pre_topc, axiom,
% 3.34/3.60    (![A:$i]:
% 3.34/3.60     ( ( l1_pre_topc @ A ) =>
% 3.34/3.60       ( ![B:$i]:
% 3.34/3.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.34/3.60           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 3.34/3.60             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 3.34/3.60               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 3.34/3.60  thf('158', plain,
% 3.34/3.60      (![X42 : $i, X43 : $i]:
% 3.34/3.60         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 3.34/3.60          | ~ (v4_pre_topc @ X42 @ X43)
% 3.34/3.60          | ((k2_pre_topc @ X43 @ X42) = (X42))
% 3.34/3.60          | ~ (l1_pre_topc @ X43))),
% 3.34/3.60      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.34/3.60  thf('159', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ X1)
% 3.34/3.60          | ~ (l1_pre_topc @ X0)
% 3.34/3.60          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 3.34/3.60          | ~ (v4_pre_topc @ X1 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['157', '158'])).
% 3.34/3.60  thf('160', plain,
% 3.34/3.60      (![X0 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ X0)
% 3.34/3.60          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 3.34/3.60          | ~ (l1_pre_topc @ sk_A)
% 3.34/3.60          | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['156', '159'])).
% 3.34/3.60  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('162', plain,
% 3.34/3.60      (![X0 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ X0)
% 3.34/3.60          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 3.34/3.60          | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('demod', [status(thm)], ['160', '161'])).
% 3.34/3.60  thf('163', plain,
% 3.34/3.60      (![X0 : $i]: (((k2_pre_topc @ sk_A @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.60      inference('simplify', [status(thm)], ['162'])).
% 3.34/3.60  thf('164', plain,
% 3.34/3.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['118', '119'])).
% 3.34/3.60  thf('165', plain,
% 3.34/3.60      (![X42 : $i, X43 : $i]:
% 3.34/3.60         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 3.34/3.60          | ~ (v2_pre_topc @ X43)
% 3.34/3.60          | ((k2_pre_topc @ X43 @ X42) != (X42))
% 3.34/3.60          | (v4_pre_topc @ X42 @ X43)
% 3.34/3.60          | ~ (l1_pre_topc @ X43))),
% 3.34/3.60      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.34/3.60  thf('166', plain,
% 3.34/3.60      (![X0 : $i]:
% 3.34/3.60         (~ (l1_pre_topc @ X0)
% 3.34/3.60          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 3.34/3.60          | ((k2_pre_topc @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 3.34/3.60          | ~ (v2_pre_topc @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['164', '165'])).
% 3.34/3.60  thf('167', plain,
% 3.34/3.60      ((((k1_xboole_0) != (k1_xboole_0))
% 3.34/3.60        | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.34/3.60        | ~ (v2_pre_topc @ sk_A)
% 3.34/3.60        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 3.34/3.60        | ~ (l1_pre_topc @ sk_A))),
% 3.34/3.60      inference('sup-', [status(thm)], ['163', '166'])).
% 3.34/3.60  thf('168', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.60  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('171', plain,
% 3.34/3.60      ((((k1_xboole_0) != (k1_xboole_0)) | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 3.34/3.60      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 3.34/3.60  thf('172', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 3.34/3.60      inference('simplify', [status(thm)], ['171'])).
% 3.34/3.60  thf('173', plain,
% 3.34/3.60      (![X0 : $i, X1 : $i]:
% 3.34/3.60         (~ (v1_xboole_0 @ X1)
% 3.34/3.60          | ~ (l1_pre_topc @ X0)
% 3.34/3.60          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 3.34/3.60          | ~ (v4_pre_topc @ X1 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['157', '158'])).
% 3.34/3.60  thf('174', plain,
% 3.34/3.60      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 3.34/3.60        | ~ (l1_pre_topc @ sk_A)
% 3.34/3.60        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['172', '173'])).
% 3.34/3.60  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('176', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.60  thf('177', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.60      inference('demod', [status(thm)], ['174', '175', '176'])).
% 3.34/3.60  thf('178', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 3.34/3.60      inference('clc', [status(thm)], ['104', '107'])).
% 3.34/3.60  thf('179', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 3.34/3.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.34/3.60  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('182', plain, (![X0 : $i]: ((k1_xboole_0) = (sk_C @ k1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['134', '135'])).
% 3.34/3.60  thf('183', plain, (![X38 : $i, X39 : $i]: (v1_funct_1 @ (sk_C @ X38 @ X39))),
% 3.34/3.60      inference('cnf', [status(esa)], [rc1_funct_2])).
% 3.34/3.60  thf('184', plain, ((v1_funct_1 @ k1_xboole_0)),
% 3.34/3.60      inference('sup+', [status(thm)], ['182', '183'])).
% 3.34/3.60  thf('185', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 3.34/3.60      inference('clc', [status(thm)], ['104', '107'])).
% 3.34/3.60  thf('186', plain, (![X0 : $i]: ((k1_xboole_0) = (sk_C @ k1_xboole_0 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['134', '135'])).
% 3.34/3.60  thf('187', plain,
% 3.34/3.60      (![X38 : $i, X39 : $i]: (v1_funct_2 @ (sk_C @ X38 @ X39) @ X39 @ X38)),
% 3.34/3.60      inference('cnf', [status(esa)], [rc1_funct_2])).
% 3.34/3.60  thf('188', plain,
% 3.34/3.60      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.34/3.60      inference('sup+', [status(thm)], ['186', '187'])).
% 3.34/3.60  thf('189', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 3.34/3.60      inference('clc', [status(thm)], ['104', '107'])).
% 3.34/3.60  thf('190', plain,
% 3.34/3.60      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.60      inference('simplify', [status(thm)], ['7'])).
% 3.34/3.60  thf('191', plain,
% 3.34/3.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.34/3.60      inference('sup-', [status(thm)], ['118', '119'])).
% 3.34/3.60  thf('192', plain, ((l1_pre_topc @ sk_B_3)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('193', plain, ((v2_pre_topc @ sk_B_3)),
% 3.34/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.60  thf('194', plain, ((v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 3.34/3.60      inference('demod', [status(thm)],
% 3.34/3.60                ['115', '116', '117', '146', '177', '178', '179', '180', 
% 3.34/3.60                 '181', '184', '185', '188', '189', '190', '191', '192', '193'])).
% 3.34/3.60  thf('195', plain, ($false), inference('demod', [status(thm)], ['58', '194'])).
% 3.34/3.60  
% 3.34/3.60  % SZS output end Refutation
% 3.34/3.60  
% 3.34/3.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
