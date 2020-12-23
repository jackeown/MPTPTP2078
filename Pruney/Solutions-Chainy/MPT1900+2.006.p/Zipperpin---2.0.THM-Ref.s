%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qiXS6wlHEM

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:45 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  275 (3804 expanded)
%              Number of leaves         :   63 (1193 expanded)
%              Depth                    :   20
%              Number of atoms          : 1893 (52012 expanded)
%              Number of equality atoms :   99 ( 973 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

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
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_2 ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( ( k2_struct_0 @ X38 )
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
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ( X5 = X6 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
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
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) )
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
    ! [X35: $i] :
      ( ( l1_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
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
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X35: $i] :
      ( ( l1_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_2 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X49 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_tdlat_3 @ X57 )
      | ( v3_pre_topc @ X58 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ X0 ) @ sk_A )
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
      ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X40: $i,X41: $i,X43: $i,X44: $i] :
      ( ( zip_tseitin_1 @ X40 @ X43 @ X41 @ X44 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X41 ) @ X43 @ X40 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X45 @ X46 @ X47 ) @ X47 @ X46 @ X45 )
      | ( v5_pre_topc @ X47 @ X45 @ X46 )
      | ~ ( zip_tseitin_2 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('58',plain,(
    ~ ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['0','57'])).

thf('59',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( ( k2_struct_0 @ X38 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('60',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ sk_B_2 ) @ X0 )
      | ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
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

thf('66',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ( m1_subset_1 @ ( sk_D_1 @ X53 @ X52 @ X54 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( v5_pre_topc @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X52 ) ) ) )
      | ~ ( v1_funct_2 @ X53 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X52 ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('67',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72','73'])).

thf('75',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['64','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('81',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('82',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_2 ) @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A )
    | ( ( k2_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','83'])).

thf('85',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('86',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('87',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A )
    | ( ( k2_struct_0 @ sk_B_2 )
      = ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( ( k2_struct_0 @ X38 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('90',plain,
    ( ( ( k2_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('92',plain,
    ( ( ( k2_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('94',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('95',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_struct_0 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['92','95'])).

thf('97',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A )
    | ( k1_xboole_0
      = ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','96'])).

thf('98',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('99',plain,
    ( k1_xboole_0
    = ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X54 @ ( k8_relset_1 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X52 ) @ X53 @ ( sk_D_1 @ X53 @ X52 @ X54 ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X52 ) @ X53 @ ( k2_pre_topc @ X52 @ ( sk_D_1 @ X53 @ X52 @ X54 ) ) ) )
      | ( v5_pre_topc @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X52 ) ) ) )
      | ~ ( v1_funct_2 @ X53 @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X52 ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('101',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ k1_xboole_0 @ ( k2_pre_topc @ sk_B_2 @ k1_xboole_0 ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('103',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('106',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A )
      = ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A )
      = ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) )
    | ( ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A )
      = ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A )
        = ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['102','113'])).

thf('115',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B_2 ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('119',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B_2 ) ) )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('122',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('123',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('124',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('126',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['121','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( k1_xboole_0
        = ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('134',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('135',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('137',plain,(
    ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('139',plain,
    ( k1_xboole_0
    = ( sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('140',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('141',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('142',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('143',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k8_relset_1 @ X31 @ X32 @ X33 @ X32 )
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('146',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('148',plain,(
    ! [X20: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('149',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('152',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['151'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('153',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('154',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['150','154'])).

thf('156',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('157',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['144','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('162',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('164',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_tdlat_3 @ X59 )
      | ( v4_pre_topc @ X60 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X59 )
      | ~ ( v2_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','165'])).

thf('167',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

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

thf('171',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v4_pre_topc @ X36 @ X37 )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = X36 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('178',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v2_pre_topc @ X37 )
      | ( ( k2_pre_topc @ X37 @ X36 )
       != X36 )
      | ( v4_pre_topc @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['176','179'])).

thf('181',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('187',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('190',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('192',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('193',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('197',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('199',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','56'])).

thf('201',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('203',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('205',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('206',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('207',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['101','138','139','159','190','191','192','193','194','197','198','203','204','205','206','207','208'])).

thf('210',plain,(
    $false ),
    inference(demod,[status(thm)],['58','209'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qiXS6wlHEM
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.44/3.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.44/3.62  % Solved by: fo/fo7.sh
% 3.44/3.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.44/3.62  % done 4306 iterations in 3.165s
% 3.44/3.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.44/3.62  % SZS output start Refutation
% 3.44/3.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.44/3.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.44/3.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.44/3.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.44/3.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 3.44/3.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.44/3.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.44/3.62  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 3.44/3.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.44/3.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.44/3.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.44/3.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.44/3.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.44/3.62  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 3.44/3.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.44/3.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.44/3.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.44/3.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.44/3.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.44/3.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.44/3.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.44/3.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.44/3.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 3.44/3.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.44/3.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.44/3.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.44/3.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.44/3.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.44/3.62  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 3.44/3.62  thf(sk_A_type, type, sk_A: $i).
% 3.44/3.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.44/3.62  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 3.44/3.62  thf(sk_C_type, type, sk_C: $i).
% 3.44/3.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.44/3.62  thf(t68_tex_2, conjecture,
% 3.44/3.62    (![A:$i]:
% 3.44/3.62     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.44/3.62       ( ![B:$i]:
% 3.44/3.62         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 3.44/3.62           ( ![C:$i]:
% 3.44/3.62             ( ( ( v1_funct_1 @ C ) & 
% 3.44/3.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.44/3.62                 ( m1_subset_1 @
% 3.44/3.62                   C @ 
% 3.44/3.62                   ( k1_zfmisc_1 @
% 3.44/3.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.44/3.62               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 3.44/3.62  thf(zf_stmt_0, negated_conjecture,
% 3.44/3.62    (~( ![A:$i]:
% 3.44/3.62        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.44/3.62          ( ![B:$i]:
% 3.44/3.62            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 3.44/3.62              ( ![C:$i]:
% 3.44/3.62                ( ( ( v1_funct_1 @ C ) & 
% 3.44/3.62                    ( v1_funct_2 @
% 3.44/3.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.44/3.62                    ( m1_subset_1 @
% 3.44/3.62                      C @ 
% 3.44/3.62                      ( k1_zfmisc_1 @
% 3.44/3.62                        ( k2_zfmisc_1 @
% 3.44/3.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.44/3.62                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 3.44/3.62    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 3.44/3.62  thf('0', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_2)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf(t55_tops_2, axiom,
% 3.44/3.62    (![A:$i]:
% 3.44/3.62     ( ( l1_pre_topc @ A ) =>
% 3.44/3.62       ( ![B:$i]:
% 3.44/3.62         ( ( l1_pre_topc @ B ) =>
% 3.44/3.62           ( ![C:$i]:
% 3.44/3.62             ( ( ( m1_subset_1 @
% 3.44/3.62                   C @ 
% 3.44/3.62                   ( k1_zfmisc_1 @
% 3.44/3.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 3.44/3.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.44/3.62                 ( v1_funct_1 @ C ) ) =>
% 3.44/3.62               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 3.44/3.62                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.44/3.62                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.44/3.62                   ( ![D:$i]:
% 3.44/3.62                     ( ( m1_subset_1 @
% 3.44/3.62                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.44/3.62                       ( ( v3_pre_topc @ D @ B ) =>
% 3.44/3.62                         ( v3_pre_topc @
% 3.44/3.62                           ( k8_relset_1 @
% 3.44/3.62                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 3.44/3.62                           A ) ) ) ) ) ) ) ) ) ) ))).
% 3.44/3.62  thf(zf_stmt_1, axiom,
% 3.44/3.62    (![B:$i,A:$i]:
% 3.44/3.62     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 3.44/3.62         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.44/3.62       ( zip_tseitin_0 @ B @ A ) ))).
% 3.44/3.62  thf('1', plain,
% 3.44/3.62      (![X38 : $i, X39 : $i]:
% 3.44/3.62         ((zip_tseitin_0 @ X38 @ X39) | ((k2_struct_0 @ X38) = (k1_xboole_0)))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.44/3.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.44/3.62  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.44/3.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.44/3.62  thf('3', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 3.44/3.62      inference('sup+', [status(thm)], ['1', '2'])).
% 3.44/3.62  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.44/3.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.44/3.62  thf(t8_boole, axiom,
% 3.44/3.62    (![A:$i,B:$i]:
% 3.44/3.62     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.44/3.62  thf('5', plain,
% 3.44/3.62      (![X5 : $i, X6 : $i]:
% 3.44/3.62         (~ (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X6) | ((X5) = (X6)))),
% 3.44/3.62      inference('cnf', [status(esa)], [t8_boole])).
% 3.44/3.62  thf('6', plain,
% 3.44/3.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['4', '5'])).
% 3.44/3.62  thf(t113_zfmisc_1, axiom,
% 3.44/3.62    (![A:$i,B:$i]:
% 3.44/3.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.44/3.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.44/3.62  thf('7', plain,
% 3.44/3.62      (![X8 : $i, X9 : $i]:
% 3.44/3.62         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 3.44/3.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.44/3.62  thf('8', plain,
% 3.44/3.62      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 3.44/3.62      inference('simplify', [status(thm)], ['7'])).
% 3.44/3.62  thf('9', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.62      inference('sup+', [status(thm)], ['6', '8'])).
% 3.44/3.62  thf(d3_struct_0, axiom,
% 3.44/3.62    (![A:$i]:
% 3.44/3.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.44/3.62  thf('10', plain,
% 3.44/3.62      (![X34 : $i]:
% 3.44/3.62         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.44/3.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.44/3.62  thf('11', plain,
% 3.44/3.62      (![X34 : $i]:
% 3.44/3.62         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.44/3.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.44/3.62  thf('12', plain,
% 3.44/3.62      ((m1_subset_1 @ sk_C @ 
% 3.44/3.62        (k1_zfmisc_1 @ 
% 3.44/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf(t3_subset, axiom,
% 3.44/3.62    (![A:$i,B:$i]:
% 3.44/3.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.44/3.62  thf('13', plain,
% 3.44/3.62      (![X12 : $i, X13 : $i]:
% 3.44/3.62         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.44/3.62      inference('cnf', [status(esa)], [t3_subset])).
% 3.44/3.62  thf('14', plain,
% 3.44/3.62      ((r1_tarski @ sk_C @ 
% 3.44/3.62        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['12', '13'])).
% 3.44/3.62  thf('15', plain,
% 3.44/3.62      (((r1_tarski @ sk_C @ 
% 3.44/3.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2)))
% 3.44/3.62        | ~ (l1_struct_0 @ sk_A))),
% 3.44/3.62      inference('sup+', [status(thm)], ['11', '14'])).
% 3.44/3.62  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf(dt_l1_pre_topc, axiom,
% 3.44/3.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.44/3.62  thf('17', plain,
% 3.44/3.62      (![X35 : $i]: ((l1_struct_0 @ X35) | ~ (l1_pre_topc @ X35))),
% 3.44/3.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.44/3.62  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 3.44/3.62      inference('sup-', [status(thm)], ['16', '17'])).
% 3.44/3.62  thf('19', plain,
% 3.44/3.62      ((r1_tarski @ sk_C @ 
% 3.44/3.62        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('demod', [status(thm)], ['15', '18'])).
% 3.44/3.62  thf('20', plain,
% 3.44/3.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['4', '5'])).
% 3.44/3.62  thf(t3_xboole_1, axiom,
% 3.44/3.62    (![A:$i]:
% 3.44/3.62     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.44/3.62  thf('21', plain,
% 3.44/3.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 3.44/3.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.44/3.62  thf('22', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         (~ (r1_tarski @ X1 @ X0)
% 3.44/3.62          | ~ (v1_xboole_0 @ X0)
% 3.44/3.62          | ((X1) = (k1_xboole_0)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['20', '21'])).
% 3.44/3.62  thf('23', plain,
% 3.44/3.62      ((((sk_C) = (k1_xboole_0))
% 3.44/3.62        | ~ (v1_xboole_0 @ 
% 3.44/3.62             (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.44/3.62      inference('sup-', [status(thm)], ['19', '22'])).
% 3.44/3.62  thf('24', plain,
% 3.44/3.62      ((~ (v1_xboole_0 @ 
% 3.44/3.62           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2)))
% 3.44/3.62        | ~ (l1_struct_0 @ sk_B_2)
% 3.44/3.62        | ((sk_C) = (k1_xboole_0)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['10', '23'])).
% 3.44/3.62  thf('25', plain, ((l1_pre_topc @ sk_B_2)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('26', plain,
% 3.44/3.62      (![X35 : $i]: ((l1_struct_0 @ X35) | ~ (l1_pre_topc @ X35))),
% 3.44/3.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.44/3.62  thf('27', plain, ((l1_struct_0 @ sk_B_2)),
% 3.44/3.62      inference('sup-', [status(thm)], ['25', '26'])).
% 3.44/3.62  thf('28', plain,
% 3.44/3.62      ((~ (v1_xboole_0 @ 
% 3.44/3.62           (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2)))
% 3.44/3.62        | ((sk_C) = (k1_xboole_0)))),
% 3.44/3.62      inference('demod', [status(thm)], ['24', '27'])).
% 3.44/3.62  thf('29', plain,
% 3.44/3.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.44/3.62        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_2))
% 3.44/3.62        | ((sk_C) = (k1_xboole_0)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['9', '28'])).
% 3.44/3.62  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.44/3.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.44/3.62  thf('31', plain,
% 3.44/3.62      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_2)) | ((sk_C) = (k1_xboole_0)))),
% 3.44/3.62      inference('demod', [status(thm)], ['29', '30'])).
% 3.44/3.62  thf('32', plain,
% 3.44/3.62      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | ((sk_C) = (k1_xboole_0)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['3', '31'])).
% 3.44/3.62  thf('33', plain,
% 3.44/3.62      ((m1_subset_1 @ sk_C @ 
% 3.44/3.62        (k1_zfmisc_1 @ 
% 3.44/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 3.44/3.62  thf(zf_stmt_3, axiom,
% 3.44/3.62    (![C:$i,B:$i,A:$i]:
% 3.44/3.62     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 3.44/3.62       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.44/3.62         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 3.44/3.62  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 3.44/3.62  thf(zf_stmt_5, axiom,
% 3.44/3.62    (![D:$i,C:$i,B:$i,A:$i]:
% 3.44/3.62     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 3.44/3.62       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.44/3.62         ( ( v3_pre_topc @ D @ B ) =>
% 3.44/3.62           ( v3_pre_topc @
% 3.44/3.62             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 3.44/3.62             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 3.44/3.62  thf(zf_stmt_7, axiom,
% 3.44/3.62    (![A:$i]:
% 3.44/3.62     ( ( l1_pre_topc @ A ) =>
% 3.44/3.62       ( ![B:$i]:
% 3.44/3.62         ( ( l1_pre_topc @ B ) =>
% 3.44/3.62           ( ![C:$i]:
% 3.44/3.62             ( ( ( v1_funct_1 @ C ) & 
% 3.44/3.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.44/3.62                 ( m1_subset_1 @
% 3.44/3.62                   C @ 
% 3.44/3.62                   ( k1_zfmisc_1 @
% 3.44/3.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.44/3.62               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 3.44/3.62  thf('34', plain,
% 3.44/3.62      (![X49 : $i, X50 : $i, X51 : $i]:
% 3.44/3.62         (~ (l1_pre_topc @ X49)
% 3.44/3.62          | ~ (zip_tseitin_0 @ X49 @ X50)
% 3.44/3.62          | (zip_tseitin_2 @ X51 @ X49 @ X50)
% 3.44/3.62          | ~ (m1_subset_1 @ X51 @ 
% 3.44/3.62               (k1_zfmisc_1 @ 
% 3.44/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X49))))
% 3.44/3.62          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X49))
% 3.44/3.62          | ~ (v1_funct_1 @ X51)
% 3.44/3.62          | ~ (l1_pre_topc @ X50))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.44/3.62  thf('35', plain,
% 3.44/3.62      ((~ (l1_pre_topc @ sk_A)
% 3.44/3.62        | ~ (v1_funct_1 @ sk_C)
% 3.44/3.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 3.44/3.62        | (zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)
% 3.44/3.62        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A)
% 3.44/3.62        | ~ (l1_pre_topc @ sk_B_2))),
% 3.44/3.62      inference('sup-', [status(thm)], ['33', '34'])).
% 3.44/3.62  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('38', plain,
% 3.44/3.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('39', plain, ((l1_pre_topc @ sk_B_2)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('40', plain,
% 3.44/3.62      (((zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)
% 3.44/3.62        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 3.44/3.62  thf('41', plain,
% 3.44/3.62      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('sup-', [status(thm)], ['32', '40'])).
% 3.44/3.62  thf('42', plain,
% 3.44/3.62      ((m1_subset_1 @ sk_C @ 
% 3.44/3.62        (k1_zfmisc_1 @ 
% 3.44/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf(dt_k8_relset_1, axiom,
% 3.44/3.62    (![A:$i,B:$i,C:$i,D:$i]:
% 3.44/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.44/3.62       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.44/3.62  thf('43', plain,
% 3.44/3.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.44/3.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.44/3.62          | (m1_subset_1 @ (k8_relset_1 @ X25 @ X26 @ X24 @ X27) @ 
% 3.44/3.62             (k1_zfmisc_1 @ X25)))),
% 3.44/3.62      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 3.44/3.62  thf('44', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         (m1_subset_1 @ 
% 3.44/3.62          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.44/3.62           sk_C @ X0) @ 
% 3.44/3.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['42', '43'])).
% 3.44/3.62  thf(t17_tdlat_3, axiom,
% 3.44/3.62    (![A:$i]:
% 3.44/3.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.44/3.62       ( ( v1_tdlat_3 @ A ) <=>
% 3.44/3.62         ( ![B:$i]:
% 3.44/3.62           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.62             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 3.44/3.62  thf('45', plain,
% 3.44/3.62      (![X57 : $i, X58 : $i]:
% 3.44/3.62         (~ (v1_tdlat_3 @ X57)
% 3.44/3.62          | (v3_pre_topc @ X58 @ X57)
% 3.44/3.62          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 3.44/3.62          | ~ (l1_pre_topc @ X57)
% 3.44/3.62          | ~ (v2_pre_topc @ X57))),
% 3.44/3.62      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 3.44/3.62  thf('46', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         (~ (v2_pre_topc @ sk_A)
% 3.44/3.62          | ~ (l1_pre_topc @ sk_A)
% 3.44/3.62          | (v3_pre_topc @ 
% 3.44/3.62             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.44/3.62              sk_C @ X0) @ 
% 3.44/3.62             sk_A)
% 3.44/3.62          | ~ (v1_tdlat_3 @ sk_A))),
% 3.44/3.62      inference('sup-', [status(thm)], ['44', '45'])).
% 3.44/3.62  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('49', plain, ((v1_tdlat_3 @ sk_A)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('50', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         (v3_pre_topc @ 
% 3.44/3.62          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.44/3.62           sk_C @ X0) @ 
% 3.44/3.62          sk_A)),
% 3.44/3.62      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 3.44/3.62  thf('51', plain,
% 3.44/3.62      (![X40 : $i, X41 : $i, X43 : $i, X44 : $i]:
% 3.44/3.62         ((zip_tseitin_1 @ X40 @ X43 @ X41 @ X44)
% 3.44/3.62          | ~ (v3_pre_topc @ 
% 3.44/3.62               (k8_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X41) @ 
% 3.44/3.62                X43 @ X40) @ 
% 3.44/3.62               X44))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.44/3.62  thf('52', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_C @ sk_B_2 @ sk_A)),
% 3.44/3.62      inference('sup-', [status(thm)], ['50', '51'])).
% 3.44/3.62  thf('53', plain,
% 3.44/3.62      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.44/3.62         (~ (zip_tseitin_1 @ (sk_D @ X45 @ X46 @ X47) @ X47 @ X46 @ X45)
% 3.44/3.62          | (v5_pre_topc @ X47 @ X45 @ X46)
% 3.44/3.62          | ~ (zip_tseitin_2 @ X47 @ X46 @ X45))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.44/3.62  thf('54', plain,
% 3.44/3.62      ((~ (zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)
% 3.44/3.62        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_2))),
% 3.44/3.62      inference('sup-', [status(thm)], ['52', '53'])).
% 3.44/3.62  thf('55', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_2)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('56', plain, (~ (zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)),
% 3.44/3.62      inference('clc', [status(thm)], ['54', '55'])).
% 3.44/3.62  thf('57', plain, (((sk_C) = (k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['41', '56'])).
% 3.44/3.62  thf('58', plain, (~ (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 3.44/3.62      inference('demod', [status(thm)], ['0', '57'])).
% 3.44/3.62  thf('59', plain,
% 3.44/3.62      (![X38 : $i, X39 : $i]:
% 3.44/3.62         ((zip_tseitin_0 @ X38 @ X39) | ((k2_struct_0 @ X38) = (k1_xboole_0)))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.44/3.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.44/3.62  thf('60', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.44/3.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.44/3.62  thf('61', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.62         ((r1_tarski @ (k2_struct_0 @ X0) @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 3.44/3.62      inference('sup+', [status(thm)], ['59', '60'])).
% 3.44/3.62  thf('62', plain,
% 3.44/3.62      (((zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)
% 3.44/3.62        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 3.44/3.62  thf('63', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         ((r1_tarski @ (k2_struct_0 @ sk_B_2) @ X0)
% 3.44/3.62          | (zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('sup-', [status(thm)], ['61', '62'])).
% 3.44/3.62  thf('64', plain,
% 3.44/3.62      (![X34 : $i]:
% 3.44/3.62         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.44/3.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.44/3.62  thf('65', plain,
% 3.44/3.62      ((m1_subset_1 @ sk_C @ 
% 3.44/3.62        (k1_zfmisc_1 @ 
% 3.44/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf(t56_tops_2, axiom,
% 3.44/3.62    (![A:$i]:
% 3.44/3.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.44/3.62       ( ![B:$i]:
% 3.44/3.62         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 3.44/3.62           ( ![C:$i]:
% 3.44/3.62             ( ( ( v1_funct_1 @ C ) & 
% 3.44/3.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.44/3.62                 ( m1_subset_1 @
% 3.44/3.62                   C @ 
% 3.44/3.62                   ( k1_zfmisc_1 @
% 3.44/3.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.44/3.62               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.44/3.62                 ( ![D:$i]:
% 3.44/3.62                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.44/3.62                     ( r1_tarski @
% 3.44/3.62                       ( k2_pre_topc @
% 3.44/3.62                         A @ 
% 3.44/3.62                         ( k8_relset_1 @
% 3.44/3.62                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 3.44/3.62                       ( k8_relset_1 @
% 3.44/3.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 3.44/3.62                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.44/3.62  thf('66', plain,
% 3.44/3.62      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.44/3.62         (~ (v2_pre_topc @ X52)
% 3.44/3.62          | ~ (l1_pre_topc @ X52)
% 3.44/3.62          | (m1_subset_1 @ (sk_D_1 @ X53 @ X52 @ X54) @ 
% 3.44/3.62             (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 3.44/3.62          | (v5_pre_topc @ X53 @ X54 @ X52)
% 3.44/3.62          | ~ (m1_subset_1 @ X53 @ 
% 3.44/3.62               (k1_zfmisc_1 @ 
% 3.44/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X52))))
% 3.44/3.62          | ~ (v1_funct_2 @ X53 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X52))
% 3.44/3.62          | ~ (v1_funct_1 @ X53)
% 3.44/3.62          | ~ (l1_pre_topc @ X54)
% 3.44/3.62          | ~ (v2_pre_topc @ X54))),
% 3.44/3.62      inference('cnf', [status(esa)], [t56_tops_2])).
% 3.44/3.62  thf('67', plain,
% 3.44/3.62      ((~ (v2_pre_topc @ sk_A)
% 3.44/3.62        | ~ (l1_pre_topc @ sk_A)
% 3.44/3.62        | ~ (v1_funct_1 @ sk_C)
% 3.44/3.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 3.44/3.62        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_2)
% 3.44/3.62        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ 
% 3.44/3.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 3.44/3.62        | ~ (l1_pre_topc @ sk_B_2)
% 3.44/3.62        | ~ (v2_pre_topc @ sk_B_2))),
% 3.44/3.62      inference('sup-', [status(thm)], ['65', '66'])).
% 3.44/3.62  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('71', plain,
% 3.44/3.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('72', plain, ((l1_pre_topc @ sk_B_2)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('73', plain, ((v2_pre_topc @ sk_B_2)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('74', plain,
% 3.44/3.62      (((v5_pre_topc @ sk_C @ sk_A @ sk_B_2)
% 3.44/3.62        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ 
% 3.44/3.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 3.44/3.62      inference('demod', [status(thm)],
% 3.44/3.62                ['67', '68', '69', '70', '71', '72', '73'])).
% 3.44/3.62  thf('75', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_2)),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.62  thf('76', plain,
% 3.44/3.62      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ 
% 3.44/3.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('clc', [status(thm)], ['74', '75'])).
% 3.44/3.62  thf('77', plain,
% 3.44/3.62      (![X12 : $i, X13 : $i]:
% 3.44/3.62         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.44/3.62      inference('cnf', [status(esa)], [t3_subset])).
% 3.44/3.62  thf('78', plain,
% 3.44/3.62      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.44/3.62      inference('sup-', [status(thm)], ['76', '77'])).
% 3.44/3.62  thf('79', plain,
% 3.44/3.62      (((r1_tarski @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ (k2_struct_0 @ sk_B_2))
% 3.44/3.62        | ~ (l1_struct_0 @ sk_B_2))),
% 3.44/3.62      inference('sup+', [status(thm)], ['64', '78'])).
% 3.44/3.62  thf('80', plain, ((l1_struct_0 @ sk_B_2)),
% 3.44/3.62      inference('sup-', [status(thm)], ['25', '26'])).
% 3.44/3.62  thf('81', plain,
% 3.44/3.62      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ (k2_struct_0 @ sk_B_2))),
% 3.44/3.62      inference('demod', [status(thm)], ['79', '80'])).
% 3.44/3.62  thf(d10_xboole_0, axiom,
% 3.44/3.62    (![A:$i,B:$i]:
% 3.44/3.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.44/3.62  thf('82', plain,
% 3.44/3.62      (![X0 : $i, X2 : $i]:
% 3.44/3.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.44/3.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.44/3.62  thf('83', plain,
% 3.44/3.62      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_2) @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A))
% 3.44/3.62        | ((k2_struct_0 @ sk_B_2) = (sk_D_1 @ sk_C @ sk_B_2 @ sk_A)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['81', '82'])).
% 3.44/3.62  thf('84', plain,
% 3.44/3.62      (((zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)
% 3.44/3.62        | ((k2_struct_0 @ sk_B_2) = (sk_D_1 @ sk_C @ sk_B_2 @ sk_A)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['63', '83'])).
% 3.44/3.62  thf('85', plain, (((sk_C) = (k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['41', '56'])).
% 3.44/3.62  thf('86', plain, (((sk_C) = (k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['41', '56'])).
% 3.44/3.62  thf('87', plain,
% 3.44/3.62      (((zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)
% 3.44/3.62        | ((k2_struct_0 @ sk_B_2) = (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A)))),
% 3.44/3.62      inference('demod', [status(thm)], ['84', '85', '86'])).
% 3.44/3.62  thf('88', plain,
% 3.44/3.62      (![X38 : $i, X39 : $i]:
% 3.44/3.62         ((zip_tseitin_0 @ X38 @ X39) | ((k2_struct_0 @ X38) = (k1_xboole_0)))),
% 3.44/3.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.44/3.62  thf('89', plain,
% 3.44/3.62      (((zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)
% 3.44/3.62        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 3.44/3.62  thf('90', plain,
% 3.44/3.62      ((((k2_struct_0 @ sk_B_2) = (k1_xboole_0))
% 3.44/3.62        | (zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('sup-', [status(thm)], ['88', '89'])).
% 3.44/3.62  thf('91', plain, (((sk_C) = (k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['41', '56'])).
% 3.44/3.62  thf('92', plain,
% 3.44/3.62      ((((k2_struct_0 @ sk_B_2) = (k1_xboole_0))
% 3.44/3.62        | (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('demod', [status(thm)], ['90', '91'])).
% 3.44/3.62  thf('93', plain, (~ (zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)),
% 3.44/3.62      inference('clc', [status(thm)], ['54', '55'])).
% 3.44/3.62  thf('94', plain, (((sk_C) = (k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['41', '56'])).
% 3.44/3.62  thf('95', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)),
% 3.44/3.62      inference('demod', [status(thm)], ['93', '94'])).
% 3.44/3.62  thf('96', plain, (((k2_struct_0 @ sk_B_2) = (k1_xboole_0))),
% 3.44/3.62      inference('clc', [status(thm)], ['92', '95'])).
% 3.44/3.62  thf('97', plain,
% 3.44/3.62      (((zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)
% 3.44/3.62        | ((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A)))),
% 3.44/3.62      inference('demod', [status(thm)], ['87', '96'])).
% 3.44/3.62  thf('98', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)),
% 3.44/3.62      inference('demod', [status(thm)], ['93', '94'])).
% 3.44/3.62  thf('99', plain, (((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('clc', [status(thm)], ['97', '98'])).
% 3.44/3.62  thf('100', plain,
% 3.44/3.62      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.44/3.62         (~ (v2_pre_topc @ X52)
% 3.44/3.62          | ~ (l1_pre_topc @ X52)
% 3.44/3.62          | ~ (r1_tarski @ 
% 3.44/3.62               (k2_pre_topc @ X54 @ 
% 3.44/3.62                (k8_relset_1 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X52) @ 
% 3.44/3.62                 X53 @ (sk_D_1 @ X53 @ X52 @ X54))) @ 
% 3.44/3.62               (k8_relset_1 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X52) @ 
% 3.44/3.62                X53 @ (k2_pre_topc @ X52 @ (sk_D_1 @ X53 @ X52 @ X54))))
% 3.44/3.62          | (v5_pre_topc @ X53 @ X54 @ X52)
% 3.44/3.62          | ~ (m1_subset_1 @ X53 @ 
% 3.44/3.62               (k1_zfmisc_1 @ 
% 3.44/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X52))))
% 3.44/3.62          | ~ (v1_funct_2 @ X53 @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X52))
% 3.44/3.62          | ~ (v1_funct_1 @ X53)
% 3.44/3.62          | ~ (l1_pre_topc @ X54)
% 3.44/3.62          | ~ (v2_pre_topc @ X54))),
% 3.44/3.62      inference('cnf', [status(esa)], [t56_tops_2])).
% 3.44/3.62  thf('101', plain,
% 3.44/3.62      ((~ (r1_tarski @ 
% 3.44/3.62           (k2_pre_topc @ sk_A @ 
% 3.44/3.62            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.44/3.62             k1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A))) @ 
% 3.44/3.62           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.44/3.62            k1_xboole_0 @ (k2_pre_topc @ sk_B_2 @ k1_xboole_0)))
% 3.44/3.62        | ~ (v2_pre_topc @ sk_A)
% 3.44/3.62        | ~ (l1_pre_topc @ sk_A)
% 3.44/3.62        | ~ (v1_funct_1 @ k1_xboole_0)
% 3.44/3.62        | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.44/3.62             (u1_struct_0 @ sk_B_2))
% 3.44/3.62        | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 3.44/3.62             (k1_zfmisc_1 @ 
% 3.44/3.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))
% 3.44/3.62        | (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2)
% 3.44/3.62        | ~ (l1_pre_topc @ sk_B_2)
% 3.44/3.62        | ~ (v2_pre_topc @ sk_B_2))),
% 3.44/3.62      inference('sup-', [status(thm)], ['99', '100'])).
% 3.44/3.62  thf('102', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 3.44/3.62      inference('sup+', [status(thm)], ['1', '2'])).
% 3.44/3.62  thf('103', plain,
% 3.44/3.62      (![X34 : $i]:
% 3.44/3.62         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.44/3.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.44/3.62  thf('104', plain,
% 3.44/3.62      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.44/3.62      inference('sup-', [status(thm)], ['76', '77'])).
% 3.44/3.62  thf('105', plain,
% 3.44/3.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['4', '5'])).
% 3.44/3.62  thf('106', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.44/3.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.44/3.62  thf('107', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.62      inference('sup+', [status(thm)], ['105', '106'])).
% 3.44/3.62  thf('108', plain,
% 3.44/3.62      (![X0 : $i, X2 : $i]:
% 3.44/3.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.44/3.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.44/3.62  thf('109', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['107', '108'])).
% 3.44/3.62  thf('110', plain,
% 3.44/3.62      ((((sk_D_1 @ sk_C @ sk_B_2 @ sk_A) = (u1_struct_0 @ sk_B_2))
% 3.44/3.62        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['104', '109'])).
% 3.44/3.62  thf('111', plain,
% 3.44/3.62      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_2))
% 3.44/3.62        | ~ (l1_struct_0 @ sk_B_2)
% 3.44/3.62        | ((sk_D_1 @ sk_C @ sk_B_2 @ sk_A) = (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['103', '110'])).
% 3.44/3.62  thf('112', plain, ((l1_struct_0 @ sk_B_2)),
% 3.44/3.62      inference('sup-', [status(thm)], ['25', '26'])).
% 3.44/3.62  thf('113', plain,
% 3.44/3.62      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_2))
% 3.44/3.62        | ((sk_D_1 @ sk_C @ sk_B_2 @ sk_A) = (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('demod', [status(thm)], ['111', '112'])).
% 3.44/3.62  thf('114', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         ((zip_tseitin_0 @ sk_B_2 @ X0)
% 3.44/3.62          | ((sk_D_1 @ sk_C @ sk_B_2 @ sk_A) = (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['102', '113'])).
% 3.44/3.62  thf('115', plain,
% 3.44/3.62      (![X34 : $i]:
% 3.44/3.62         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.44/3.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.44/3.62  thf('116', plain,
% 3.44/3.62      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ 
% 3.44/3.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('clc', [status(thm)], ['74', '75'])).
% 3.44/3.62  thf('117', plain,
% 3.44/3.62      (((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ 
% 3.44/3.62         (k1_zfmisc_1 @ (k2_struct_0 @ sk_B_2)))
% 3.44/3.62        | ~ (l1_struct_0 @ sk_B_2))),
% 3.44/3.62      inference('sup+', [status(thm)], ['115', '116'])).
% 3.44/3.62  thf('118', plain, ((l1_struct_0 @ sk_B_2)),
% 3.44/3.62      inference('sup-', [status(thm)], ['25', '26'])).
% 3.44/3.62  thf('119', plain,
% 3.44/3.62      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B_2 @ sk_A) @ 
% 3.44/3.62        (k1_zfmisc_1 @ (k2_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('demod', [status(thm)], ['117', '118'])).
% 3.44/3.62  thf('120', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         ((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 3.44/3.62           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B_2)))
% 3.44/3.62          | (zip_tseitin_0 @ sk_B_2 @ X0))),
% 3.44/3.62      inference('sup+', [status(thm)], ['114', '119'])).
% 3.44/3.62  thf('121', plain,
% 3.44/3.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['4', '5'])).
% 3.44/3.62  thf('122', plain,
% 3.44/3.62      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 3.44/3.62      inference('simplify', [status(thm)], ['7'])).
% 3.44/3.62  thf(cc4_relset_1, axiom,
% 3.44/3.62    (![A:$i,B:$i]:
% 3.44/3.62     ( ( v1_xboole_0 @ A ) =>
% 3.44/3.62       ( ![C:$i]:
% 3.44/3.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 3.44/3.62           ( v1_xboole_0 @ C ) ) ) ))).
% 3.44/3.62  thf('123', plain,
% 3.44/3.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.44/3.62         (~ (v1_xboole_0 @ X21)
% 3.44/3.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 3.44/3.62          | (v1_xboole_0 @ X22))),
% 3.44/3.62      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.44/3.62  thf('124', plain,
% 3.44/3.62      (![X1 : $i]:
% 3.44/3.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.44/3.62          | (v1_xboole_0 @ X1)
% 3.44/3.62          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['122', '123'])).
% 3.44/3.62  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.44/3.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.44/3.62  thf('126', plain,
% 3.44/3.62      (![X1 : $i]:
% 3.44/3.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.44/3.62          | (v1_xboole_0 @ X1))),
% 3.44/3.62      inference('demod', [status(thm)], ['124', '125'])).
% 3.44/3.62  thf('127', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 3.44/3.62          | ~ (v1_xboole_0 @ X0)
% 3.44/3.62          | (v1_xboole_0 @ X1))),
% 3.44/3.62      inference('sup-', [status(thm)], ['121', '126'])).
% 3.44/3.62  thf('128', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         ((zip_tseitin_0 @ sk_B_2 @ X0)
% 3.44/3.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 3.44/3.62          | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['120', '127'])).
% 3.44/3.62  thf('129', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 3.44/3.62      inference('sup+', [status(thm)], ['1', '2'])).
% 3.44/3.62  thf('130', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 3.44/3.62          | (zip_tseitin_0 @ sk_B_2 @ X0))),
% 3.44/3.62      inference('clc', [status(thm)], ['128', '129'])).
% 3.44/3.62  thf('131', plain,
% 3.44/3.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['4', '5'])).
% 3.44/3.62  thf('132', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         ((zip_tseitin_0 @ sk_B_2 @ X0)
% 3.44/3.62          | ((k1_xboole_0) = (u1_struct_0 @ sk_B_2)))),
% 3.44/3.62      inference('sup-', [status(thm)], ['130', '131'])).
% 3.44/3.62  thf('133', plain,
% 3.44/3.62      (((zip_tseitin_2 @ sk_C @ sk_B_2 @ sk_A)
% 3.44/3.62        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 3.44/3.62  thf('134', plain, (((sk_C) = (k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['41', '56'])).
% 3.44/3.62  thf('135', plain,
% 3.44/3.62      (((zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)
% 3.44/3.62        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('demod', [status(thm)], ['133', '134'])).
% 3.44/3.62  thf('136', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_2 @ sk_A)),
% 3.44/3.62      inference('demod', [status(thm)], ['93', '94'])).
% 3.44/3.62  thf('137', plain, (~ (zip_tseitin_0 @ sk_B_2 @ sk_A)),
% 3.44/3.62      inference('clc', [status(thm)], ['135', '136'])).
% 3.44/3.62  thf('138', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B_2))),
% 3.44/3.62      inference('sup-', [status(thm)], ['132', '137'])).
% 3.44/3.62  thf('139', plain, (((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_2 @ sk_A))),
% 3.44/3.62      inference('clc', [status(thm)], ['97', '98'])).
% 3.44/3.62  thf('140', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.44/3.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.44/3.62  thf('141', plain,
% 3.44/3.62      (![X12 : $i, X14 : $i]:
% 3.44/3.62         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 3.44/3.62      inference('cnf', [status(esa)], [t3_subset])).
% 3.44/3.62  thf('142', plain,
% 3.44/3.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['140', '141'])).
% 3.44/3.62  thf(t38_relset_1, axiom,
% 3.44/3.62    (![A:$i,B:$i,C:$i]:
% 3.44/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.44/3.62       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 3.44/3.62         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.44/3.62  thf('143', plain,
% 3.44/3.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.44/3.62         (((k8_relset_1 @ X31 @ X32 @ X33 @ X32)
% 3.44/3.62            = (k1_relset_1 @ X31 @ X32 @ X33))
% 3.44/3.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 3.44/3.62      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.44/3.62  thf('144', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 3.44/3.62           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['142', '143'])).
% 3.44/3.62  thf('145', plain,
% 3.44/3.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['140', '141'])).
% 3.44/3.62  thf(redefinition_k1_relset_1, axiom,
% 3.44/3.62    (![A:$i,B:$i,C:$i]:
% 3.44/3.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.44/3.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.44/3.62  thf('146', plain,
% 3.44/3.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.44/3.62         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 3.44/3.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 3.44/3.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.44/3.62  thf('147', plain,
% 3.44/3.62      (![X0 : $i, X1 : $i]:
% 3.44/3.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.44/3.62      inference('sup-', [status(thm)], ['145', '146'])).
% 3.44/3.62  thf(l222_relat_1, axiom,
% 3.44/3.62    (![A:$i,B:$i]:
% 3.44/3.62     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 3.44/3.62  thf('148', plain, (![X20 : $i]: (v4_relat_1 @ k1_xboole_0 @ X20)),
% 3.44/3.62      inference('cnf', [status(esa)], [l222_relat_1])).
% 3.44/3.62  thf(d18_relat_1, axiom,
% 3.44/3.62    (![A:$i,B:$i]:
% 3.44/3.62     ( ( v1_relat_1 @ B ) =>
% 3.44/3.62       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.44/3.62  thf('149', plain,
% 3.44/3.62      (![X15 : $i, X16 : $i]:
% 3.44/3.62         (~ (v4_relat_1 @ X15 @ X16)
% 3.44/3.62          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 3.44/3.62          | ~ (v1_relat_1 @ X15))),
% 3.44/3.62      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.44/3.62  thf('150', plain,
% 3.44/3.62      (![X0 : $i]:
% 3.44/3.62         (~ (v1_relat_1 @ k1_xboole_0)
% 3.44/3.63          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['148', '149'])).
% 3.44/3.63  thf('151', plain,
% 3.44/3.63      (![X8 : $i, X9 : $i]:
% 3.44/3.63         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 3.44/3.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.44/3.63  thf('152', plain,
% 3.44/3.63      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 3.44/3.63      inference('simplify', [status(thm)], ['151'])).
% 3.44/3.63  thf(fc6_relat_1, axiom,
% 3.44/3.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.44/3.63  thf('153', plain,
% 3.44/3.63      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 3.44/3.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.44/3.63  thf('154', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.44/3.63      inference('sup+', [status(thm)], ['152', '153'])).
% 3.44/3.63  thf('155', plain,
% 3.44/3.63      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 3.44/3.63      inference('demod', [status(thm)], ['150', '154'])).
% 3.44/3.63  thf('156', plain,
% 3.44/3.63      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 3.44/3.63      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.44/3.63  thf('157', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['155', '156'])).
% 3.44/3.63  thf('158', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.44/3.63      inference('demod', [status(thm)], ['147', '157'])).
% 3.44/3.63  thf('159', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.44/3.63      inference('demod', [status(thm)], ['144', '158'])).
% 3.44/3.63  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('161', plain,
% 3.44/3.63      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['4', '5'])).
% 3.44/3.63  thf('162', plain,
% 3.44/3.63      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['140', '141'])).
% 3.44/3.63  thf('163', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.63      inference('sup+', [status(thm)], ['161', '162'])).
% 3.44/3.63  thf(t18_tdlat_3, axiom,
% 3.44/3.63    (![A:$i]:
% 3.44/3.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.44/3.63       ( ( v1_tdlat_3 @ A ) <=>
% 3.44/3.63         ( ![B:$i]:
% 3.44/3.63           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.63             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 3.44/3.63  thf('164', plain,
% 3.44/3.63      (![X59 : $i, X60 : $i]:
% 3.44/3.63         (~ (v1_tdlat_3 @ X59)
% 3.44/3.63          | (v4_pre_topc @ X60 @ X59)
% 3.44/3.63          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 3.44/3.63          | ~ (l1_pre_topc @ X59)
% 3.44/3.63          | ~ (v2_pre_topc @ X59))),
% 3.44/3.63      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 3.44/3.63  thf('165', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         (~ (v1_xboole_0 @ X1)
% 3.44/3.63          | ~ (v2_pre_topc @ X0)
% 3.44/3.63          | ~ (l1_pre_topc @ X0)
% 3.44/3.63          | (v4_pre_topc @ X1 @ X0)
% 3.44/3.63          | ~ (v1_tdlat_3 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['163', '164'])).
% 3.44/3.63  thf('166', plain,
% 3.44/3.63      (![X0 : $i]:
% 3.44/3.63         (~ (v1_tdlat_3 @ sk_A)
% 3.44/3.63          | (v4_pre_topc @ X0 @ sk_A)
% 3.44/3.63          | ~ (v2_pre_topc @ sk_A)
% 3.44/3.63          | ~ (v1_xboole_0 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['160', '165'])).
% 3.44/3.63  thf('167', plain, ((v1_tdlat_3 @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('168', plain, ((v2_pre_topc @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('169', plain,
% 3.44/3.63      (![X0 : $i]: ((v4_pre_topc @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.63      inference('demod', [status(thm)], ['166', '167', '168'])).
% 3.44/3.63  thf('170', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.63      inference('sup+', [status(thm)], ['161', '162'])).
% 3.44/3.63  thf(t52_pre_topc, axiom,
% 3.44/3.63    (![A:$i]:
% 3.44/3.63     ( ( l1_pre_topc @ A ) =>
% 3.44/3.63       ( ![B:$i]:
% 3.44/3.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.63           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 3.44/3.63             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 3.44/3.63               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 3.44/3.63  thf('171', plain,
% 3.44/3.63      (![X36 : $i, X37 : $i]:
% 3.44/3.63         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 3.44/3.63          | ~ (v4_pre_topc @ X36 @ X37)
% 3.44/3.63          | ((k2_pre_topc @ X37 @ X36) = (X36))
% 3.44/3.63          | ~ (l1_pre_topc @ X37))),
% 3.44/3.63      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.44/3.63  thf('172', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         (~ (v1_xboole_0 @ X1)
% 3.44/3.63          | ~ (l1_pre_topc @ X0)
% 3.44/3.63          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 3.44/3.63          | ~ (v4_pre_topc @ X1 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['170', '171'])).
% 3.44/3.63  thf('173', plain,
% 3.44/3.63      (![X0 : $i]:
% 3.44/3.63         (~ (v1_xboole_0 @ X0)
% 3.44/3.63          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 3.44/3.63          | ~ (l1_pre_topc @ sk_A)
% 3.44/3.63          | ~ (v1_xboole_0 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['169', '172'])).
% 3.44/3.63  thf('174', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('175', plain,
% 3.44/3.63      (![X0 : $i]:
% 3.44/3.63         (~ (v1_xboole_0 @ X0)
% 3.44/3.63          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 3.44/3.63          | ~ (v1_xboole_0 @ X0))),
% 3.44/3.63      inference('demod', [status(thm)], ['173', '174'])).
% 3.44/3.63  thf('176', plain,
% 3.44/3.63      (![X0 : $i]: (((k2_pre_topc @ sk_A @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.63      inference('simplify', [status(thm)], ['175'])).
% 3.44/3.63  thf('177', plain,
% 3.44/3.63      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['140', '141'])).
% 3.44/3.63  thf('178', plain,
% 3.44/3.63      (![X36 : $i, X37 : $i]:
% 3.44/3.63         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 3.44/3.63          | ~ (v2_pre_topc @ X37)
% 3.44/3.63          | ((k2_pre_topc @ X37 @ X36) != (X36))
% 3.44/3.63          | (v4_pre_topc @ X36 @ X37)
% 3.44/3.63          | ~ (l1_pre_topc @ X37))),
% 3.44/3.63      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.44/3.63  thf('179', plain,
% 3.44/3.63      (![X0 : $i]:
% 3.44/3.63         (~ (l1_pre_topc @ X0)
% 3.44/3.63          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 3.44/3.63          | ((k2_pre_topc @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 3.44/3.63          | ~ (v2_pre_topc @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['177', '178'])).
% 3.44/3.63  thf('180', plain,
% 3.44/3.63      ((((k1_xboole_0) != (k1_xboole_0))
% 3.44/3.63        | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.44/3.63        | ~ (v2_pre_topc @ sk_A)
% 3.44/3.63        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 3.44/3.63        | ~ (l1_pre_topc @ sk_A))),
% 3.44/3.63      inference('sup-', [status(thm)], ['176', '179'])).
% 3.44/3.63  thf('181', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.44/3.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.44/3.63  thf('182', plain, ((v2_pre_topc @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('184', plain,
% 3.44/3.63      ((((k1_xboole_0) != (k1_xboole_0)) | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 3.44/3.63      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 3.44/3.63  thf('185', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 3.44/3.63      inference('simplify', [status(thm)], ['184'])).
% 3.44/3.63  thf('186', plain,
% 3.44/3.63      (![X0 : $i, X1 : $i]:
% 3.44/3.63         (~ (v1_xboole_0 @ X1)
% 3.44/3.63          | ~ (l1_pre_topc @ X0)
% 3.44/3.63          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 3.44/3.63          | ~ (v4_pre_topc @ X1 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['170', '171'])).
% 3.44/3.63  thf('187', plain,
% 3.44/3.63      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 3.44/3.63        | ~ (l1_pre_topc @ sk_A)
% 3.44/3.63        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['185', '186'])).
% 3.44/3.63  thf('188', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('189', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.44/3.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.44/3.63  thf('190', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 3.44/3.63      inference('demod', [status(thm)], ['187', '188', '189'])).
% 3.44/3.63  thf('191', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B_2))),
% 3.44/3.63      inference('sup-', [status(thm)], ['132', '137'])).
% 3.44/3.63  thf('192', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.44/3.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.44/3.63  thf('193', plain, ((v2_pre_topc @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('196', plain, (((sk_C) = (k1_xboole_0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['41', '56'])).
% 3.44/3.63  thf('197', plain, ((v1_funct_1 @ k1_xboole_0)),
% 3.44/3.63      inference('demod', [status(thm)], ['195', '196'])).
% 3.44/3.63  thf('198', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B_2))),
% 3.44/3.63      inference('sup-', [status(thm)], ['132', '137'])).
% 3.44/3.63  thf('199', plain,
% 3.44/3.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('200', plain, (((sk_C) = (k1_xboole_0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['41', '56'])).
% 3.44/3.63  thf('201', plain,
% 3.44/3.63      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.44/3.63        (u1_struct_0 @ sk_B_2))),
% 3.44/3.63      inference('demod', [status(thm)], ['199', '200'])).
% 3.44/3.63  thf('202', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B_2))),
% 3.44/3.63      inference('sup-', [status(thm)], ['132', '137'])).
% 3.44/3.63  thf('203', plain,
% 3.44/3.63      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 3.44/3.63      inference('demod', [status(thm)], ['201', '202'])).
% 3.44/3.63  thf('204', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B_2))),
% 3.44/3.63      inference('sup-', [status(thm)], ['132', '137'])).
% 3.44/3.63  thf('205', plain,
% 3.44/3.63      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 3.44/3.63      inference('simplify', [status(thm)], ['7'])).
% 3.44/3.63  thf('206', plain,
% 3.44/3.63      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.44/3.63      inference('sup-', [status(thm)], ['140', '141'])).
% 3.44/3.63  thf('207', plain, ((l1_pre_topc @ sk_B_2)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('208', plain, ((v2_pre_topc @ sk_B_2)),
% 3.44/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.63  thf('209', plain, ((v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 3.44/3.63      inference('demod', [status(thm)],
% 3.44/3.63                ['101', '138', '139', '159', '190', '191', '192', '193', 
% 3.44/3.63                 '194', '197', '198', '203', '204', '205', '206', '207', '208'])).
% 3.44/3.63  thf('210', plain, ($false), inference('demod', [status(thm)], ['58', '209'])).
% 3.44/3.63  
% 3.44/3.63  % SZS output end Refutation
% 3.44/3.63  
% 3.44/3.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
