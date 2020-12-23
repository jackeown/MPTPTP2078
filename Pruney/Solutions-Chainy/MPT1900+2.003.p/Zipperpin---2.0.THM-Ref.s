%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YmrR8keot9

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:44 EST 2020

% Result     : Theorem 4.80s
% Output     : Refutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  293 (4210 expanded)
%              Number of leaves         :   68 (1331 expanded)
%              Depth                    :   20
%              Number of atoms          : 2000 (54936 expanded)
%              Number of equality atoms :  100 ( 993 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

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
    ! [X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 )
      | ( ( k2_struct_0 @ X45 )
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X42: $i] :
      ( ( l1_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X42: $i] :
      ( ( l1_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_3 @ X0 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( zip_tseitin_0 @ X56 @ X57 )
      | ( zip_tseitin_2 @ X58 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X56 ) ) ) )
      | ~ ( v1_funct_2 @ X58 @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X56 ) )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('49',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v1_tdlat_3 @ X64 )
      | ( v3_pre_topc @ X65 @ X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( l1_pre_topc @ X64 )
      | ~ ( v2_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X47: $i,X48: $i,X50: $i,X51: $i] :
      ( ( zip_tseitin_1 @ X47 @ X50 @ X48 @ X51 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X48 ) @ X50 @ X47 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X52 @ X53 @ X54 ) @ X54 @ X53 @ X52 )
      | ( v5_pre_topc @ X54 @ X52 @ X53 )
      | ~ ( zip_tseitin_2 @ X54 @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','60'])).

thf('62',plain,(
    ~ ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ) ),
    inference(demod,[status(thm)],['0','61'])).

thf('63',plain,(
    ! [X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 )
      | ( ( k2_struct_0 @ X45 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ sk_B_3 ) @ X0 )
      | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( v2_pre_topc @ X59 )
      | ~ ( l1_pre_topc @ X59 )
      | ( m1_subset_1 @ ( sk_D_1 @ X60 @ X59 @ X61 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( v5_pre_topc @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X59 ) ) ) )
      | ~ ( v1_funct_2 @ X60 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X59 ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( v2_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('71',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_pre_topc @ sk_B_3 )
    | ~ ( v2_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('82',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['68','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('85',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B_3 ) @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ( ( k2_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','87'])).

thf('89',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','60'])).

thf('90',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','60'])).

thf('91',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    | ( ( k2_struct_0 @ sk_B_3 )
      = ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 )
      | ( ( k2_struct_0 @ X45 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('93',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('94',plain,
    ( ( ( k2_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','60'])).

thf('96',plain,
    ( ( ( k2_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('98',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','60'])).

thf('99',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['96','99'])).

thf('101',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    | ( k1_xboole_0
      = ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','100'])).

thf('102',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('103',plain,
    ( k1_xboole_0
    = ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( v2_pre_topc @ X59 )
      | ~ ( l1_pre_topc @ X59 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X61 @ ( k8_relset_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X59 ) @ X60 @ ( sk_D_1 @ X60 @ X59 @ X61 ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X59 ) @ X60 @ ( k2_pre_topc @ X59 @ ( sk_D_1 @ X60 @ X59 @ X61 ) ) ) )
      | ( v5_pre_topc @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X59 ) ) ) )
      | ~ ( v1_funct_2 @ X60 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X59 ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( v2_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('105',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ k1_xboole_0 @ ( k2_pre_topc @ sk_B_3 @ k1_xboole_0 ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) )
    | ( v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 )
    | ~ ( l1_pre_topc @ sk_B_3 )
    | ~ ( v2_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('107',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('110',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = ( u1_struct_0 @ sk_B_3 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('115',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) )
    | ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
      = ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_3 @ X0 )
      | ( ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A )
        = ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['106','115'])).

thf('117',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('119',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B_3 ) ) )
    | ~ ( l1_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('121',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B_3 ) ) )
      | ( zip_tseitin_0 @ sk_B_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('124',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('125',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('126',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('128',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_3 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['122','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
      | ( zip_tseitin_0 @ sk_B_3 @ X0 ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_3 @ X0 )
      | ( ( u1_struct_0 @ sk_B_3 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('136',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','60'])).

thf('137',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('139',plain,(
    ~ ( zip_tseitin_0 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,
    ( k1_xboole_0
    = ( sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('142',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('143',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('145',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k8_relset_1 @ X34 @ X35 @ X36 @ X35 )
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('148',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('151',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('152',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('154',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('158',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X39: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X39 ) @ X39 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('160',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['158','159'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('161',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_partfun1 @ X38 @ X37 )
      | ( ( k1_relat_1 @ X38 )
        = X37 )
      | ~ ( v4_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('164',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['163'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('165',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('166',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('168',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('169',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['162','166','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','171'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('175',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('177',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v1_tdlat_3 @ X66 )
      | ( v4_pre_topc @ X67 @ X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ~ ( l1_pre_topc @ X66 )
      | ~ ( v2_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','178'])).

thf('180',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

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

thf('184',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v4_pre_topc @ X43 @ X44 )
      | ( ( k2_pre_topc @ X44 @ X43 )
        = X43 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('191',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_pre_topc @ X44 )
      | ( ( k2_pre_topc @ X44 @ X43 )
       != X43 )
      | ( v4_pre_topc @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['189','192'])).

thf('194',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('195',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('200',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('203',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','139'])).

thf('205',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('206',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','60'])).

thf('210',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','139'])).

thf('212',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','60'])).

thf('214',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','139'])).

thf('216',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ( u1_struct_0 @ sk_B_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','139'])).

thf('218',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('219',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('220',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3 ),
    inference(demod,[status(thm)],['105','140','141','172','203','204','205','206','207','210','211','216','217','218','219','220','221'])).

thf('223',plain,(
    $false ),
    inference(demod,[status(thm)],['62','222'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YmrR8keot9
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:06:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.80/4.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.80/4.99  % Solved by: fo/fo7.sh
% 4.80/4.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.80/4.99  % done 5807 iterations in 4.519s
% 4.80/4.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.80/4.99  % SZS output start Refutation
% 4.80/4.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 4.80/4.99  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 4.80/4.99  thf(sk_B_3_type, type, sk_B_3: $i).
% 4.80/4.99  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.80/4.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.80/4.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.80/4.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.80/4.99  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.80/4.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.80/4.99  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.80/4.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.80/4.99  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 4.80/4.99  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 4.80/4.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.80/4.99  thf(sk_A_type, type, sk_A: $i).
% 4.80/4.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.80/4.99  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 4.80/4.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.80/4.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.80/4.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.80/4.99  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 4.80/4.99  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.80/4.99  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.80/4.99  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.80/4.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.80/4.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.80/4.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.80/4.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.80/4.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.80/4.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.80/4.99  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 4.80/4.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.80/4.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.80/4.99  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.80/4.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.80/4.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.80/4.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.80/4.99  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 4.80/4.99  thf(t68_tex_2, conjecture,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.80/4.99       ( ![B:$i]:
% 4.80/4.99         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.80/4.99           ( ![C:$i]:
% 4.80/4.99             ( ( ( v1_funct_1 @ C ) & 
% 4.80/4.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.80/4.99                 ( m1_subset_1 @
% 4.80/4.99                   C @ 
% 4.80/4.99                   ( k1_zfmisc_1 @
% 4.80/4.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.80/4.99               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 4.80/4.99  thf(zf_stmt_0, negated_conjecture,
% 4.80/4.99    (~( ![A:$i]:
% 4.80/4.99        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.80/4.99          ( ![B:$i]:
% 4.80/4.99            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.80/4.99              ( ![C:$i]:
% 4.80/4.99                ( ( ( v1_funct_1 @ C ) & 
% 4.80/4.99                    ( v1_funct_2 @
% 4.80/4.99                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.80/4.99                    ( m1_subset_1 @
% 4.80/4.99                      C @ 
% 4.80/4.99                      ( k1_zfmisc_1 @
% 4.80/4.99                        ( k2_zfmisc_1 @
% 4.80/4.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.80/4.99                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 4.80/4.99    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 4.80/4.99  thf('0', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf(t55_tops_2, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( l1_pre_topc @ A ) =>
% 4.80/4.99       ( ![B:$i]:
% 4.80/4.99         ( ( l1_pre_topc @ B ) =>
% 4.80/4.99           ( ![C:$i]:
% 4.80/4.99             ( ( ( m1_subset_1 @
% 4.80/4.99                   C @ 
% 4.80/4.99                   ( k1_zfmisc_1 @
% 4.80/4.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 4.80/4.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.80/4.99                 ( v1_funct_1 @ C ) ) =>
% 4.80/4.99               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 4.80/4.99                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.80/4.99                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.80/4.99                   ( ![D:$i]:
% 4.80/4.99                     ( ( m1_subset_1 @
% 4.80/4.99                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.80/4.99                       ( ( v3_pre_topc @ D @ B ) =>
% 4.80/4.99                         ( v3_pre_topc @
% 4.80/4.99                           ( k8_relset_1 @
% 4.80/4.99                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.80/4.99                           A ) ) ) ) ) ) ) ) ) ) ))).
% 4.80/4.99  thf(zf_stmt_1, axiom,
% 4.80/4.99    (![B:$i,A:$i]:
% 4.80/4.99     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 4.80/4.99         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.80/4.99       ( zip_tseitin_0 @ B @ A ) ))).
% 4.80/4.99  thf('1', plain,
% 4.80/4.99      (![X45 : $i, X46 : $i]:
% 4.80/4.99         ((zip_tseitin_0 @ X45 @ X46) | ((k2_struct_0 @ X45) = (k1_xboole_0)))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/4.99  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.80/4.99  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.80/4.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.80/4.99  thf('3', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 4.80/4.99      inference('sup+', [status(thm)], ['1', '2'])).
% 4.80/4.99  thf(d3_tarski, axiom,
% 4.80/4.99    (![A:$i,B:$i]:
% 4.80/4.99     ( ( r1_tarski @ A @ B ) <=>
% 4.80/4.99       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.80/4.99  thf('4', plain,
% 4.80/4.99      (![X4 : $i, X6 : $i]:
% 4.80/4.99         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 4.80/4.99      inference('cnf', [status(esa)], [d3_tarski])).
% 4.80/4.99  thf(d1_xboole_0, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.80/4.99  thf('5', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.80/4.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.80/4.99  thf('6', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['4', '5'])).
% 4.80/4.99  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.80/4.99  thf('7', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 4.80/4.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.80/4.99  thf(d10_xboole_0, axiom,
% 4.80/4.99    (![A:$i,B:$i]:
% 4.80/4.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.80/4.99  thf('8', plain,
% 4.80/4.99      (![X7 : $i, X9 : $i]:
% 4.80/4.99         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.80/4.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.80/4.99  thf('9', plain,
% 4.80/4.99      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['7', '8'])).
% 4.80/4.99  thf('10', plain,
% 4.80/4.99      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['6', '9'])).
% 4.80/4.99  thf(t113_zfmisc_1, axiom,
% 4.80/4.99    (![A:$i,B:$i]:
% 4.80/4.99     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.80/4.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.80/4.99  thf('11', plain,
% 4.80/4.99      (![X12 : $i, X13 : $i]:
% 4.80/4.99         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 4.80/4.99          | ((X13) != (k1_xboole_0)))),
% 4.80/4.99      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.80/4.99  thf('12', plain,
% 4.80/4.99      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 4.80/4.99      inference('simplify', [status(thm)], ['11'])).
% 4.80/4.99  thf('13', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('sup+', [status(thm)], ['10', '12'])).
% 4.80/4.99  thf(d3_struct_0, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.80/4.99  thf('14', plain,
% 4.80/4.99      (![X41 : $i]:
% 4.80/4.99         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.80/4.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.80/4.99  thf('15', plain,
% 4.80/4.99      (![X41 : $i]:
% 4.80/4.99         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.80/4.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.80/4.99  thf('16', plain,
% 4.80/4.99      ((m1_subset_1 @ sk_C_1 @ 
% 4.80/4.99        (k1_zfmisc_1 @ 
% 4.80/4.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf(t3_subset, axiom,
% 4.80/4.99    (![A:$i,B:$i]:
% 4.80/4.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.80/4.99  thf('17', plain,
% 4.80/4.99      (![X16 : $i, X17 : $i]:
% 4.80/4.99         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 4.80/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.80/4.99  thf('18', plain,
% 4.80/4.99      ((r1_tarski @ sk_C_1 @ 
% 4.80/4.99        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['16', '17'])).
% 4.80/4.99  thf('19', plain,
% 4.80/4.99      (((r1_tarski @ sk_C_1 @ 
% 4.80/4.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))
% 4.80/4.99        | ~ (l1_struct_0 @ sk_A))),
% 4.80/4.99      inference('sup+', [status(thm)], ['15', '18'])).
% 4.80/4.99  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf(dt_l1_pre_topc, axiom,
% 4.80/4.99    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 4.80/4.99  thf('21', plain,
% 4.80/4.99      (![X42 : $i]: ((l1_struct_0 @ X42) | ~ (l1_pre_topc @ X42))),
% 4.80/4.99      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.80/4.99  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 4.80/4.99      inference('sup-', [status(thm)], ['20', '21'])).
% 4.80/4.99  thf('23', plain,
% 4.80/4.99      ((r1_tarski @ sk_C_1 @ 
% 4.80/4.99        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('demod', [status(thm)], ['19', '22'])).
% 4.80/4.99  thf('24', plain,
% 4.80/4.99      (((r1_tarski @ sk_C_1 @ 
% 4.80/4.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_3)))
% 4.80/4.99        | ~ (l1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('sup+', [status(thm)], ['14', '23'])).
% 4.80/4.99  thf('25', plain, ((l1_pre_topc @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('26', plain,
% 4.80/4.99      (![X42 : $i]: ((l1_struct_0 @ X42) | ~ (l1_pre_topc @ X42))),
% 4.80/4.99      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.80/4.99  thf('27', plain, ((l1_struct_0 @ sk_B_3)),
% 4.80/4.99      inference('sup-', [status(thm)], ['25', '26'])).
% 4.80/4.99  thf('28', plain,
% 4.80/4.99      ((r1_tarski @ sk_C_1 @ 
% 4.80/4.99        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('demod', [status(thm)], ['24', '27'])).
% 4.80/4.99  thf('29', plain,
% 4.80/4.99      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['6', '9'])).
% 4.80/4.99  thf('30', plain,
% 4.80/4.99      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['7', '8'])).
% 4.80/4.99  thf('31', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (~ (r1_tarski @ X1 @ X0)
% 4.80/4.99          | ~ (v1_xboole_0 @ X0)
% 4.80/4.99          | ((X1) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['29', '30'])).
% 4.80/4.99  thf('32', plain,
% 4.80/4.99      ((((sk_C_1) = (k1_xboole_0))
% 4.80/4.99        | ~ (v1_xboole_0 @ 
% 4.80/4.99             (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_3))))),
% 4.80/4.99      inference('sup-', [status(thm)], ['28', '31'])).
% 4.80/4.99  thf('33', plain,
% 4.80/4.99      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.80/4.99        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 4.80/4.99        | ((sk_C_1) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['13', '32'])).
% 4.80/4.99  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.80/4.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.80/4.99  thf('35', plain,
% 4.80/4.99      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3)) | ((sk_C_1) = (k1_xboole_0)))),
% 4.80/4.99      inference('demod', [status(thm)], ['33', '34'])).
% 4.80/4.99  thf('36', plain,
% 4.80/4.99      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_3 @ X0) | ((sk_C_1) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['3', '35'])).
% 4.80/4.99  thf('37', plain,
% 4.80/4.99      ((m1_subset_1 @ sk_C_1 @ 
% 4.80/4.99        (k1_zfmisc_1 @ 
% 4.80/4.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 4.80/4.99  thf(zf_stmt_3, axiom,
% 4.80/4.99    (![C:$i,B:$i,A:$i]:
% 4.80/4.99     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 4.80/4.99       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.80/4.99         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 4.80/4.99  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 4.80/4.99  thf(zf_stmt_5, axiom,
% 4.80/4.99    (![D:$i,C:$i,B:$i,A:$i]:
% 4.80/4.99     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 4.80/4.99       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.80/4.99         ( ( v3_pre_topc @ D @ B ) =>
% 4.80/4.99           ( v3_pre_topc @
% 4.80/4.99             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.80/4.99             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 4.80/4.99  thf(zf_stmt_7, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( l1_pre_topc @ A ) =>
% 4.80/4.99       ( ![B:$i]:
% 4.80/4.99         ( ( l1_pre_topc @ B ) =>
% 4.80/4.99           ( ![C:$i]:
% 4.80/4.99             ( ( ( v1_funct_1 @ C ) & 
% 4.80/4.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.80/4.99                 ( m1_subset_1 @
% 4.80/4.99                   C @ 
% 4.80/4.99                   ( k1_zfmisc_1 @
% 4.80/4.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.80/4.99               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 4.80/4.99  thf('38', plain,
% 4.80/4.99      (![X56 : $i, X57 : $i, X58 : $i]:
% 4.80/4.99         (~ (l1_pre_topc @ X56)
% 4.80/4.99          | ~ (zip_tseitin_0 @ X56 @ X57)
% 4.80/4.99          | (zip_tseitin_2 @ X58 @ X56 @ X57)
% 4.80/4.99          | ~ (m1_subset_1 @ X58 @ 
% 4.80/4.99               (k1_zfmisc_1 @ 
% 4.80/4.99                (k2_zfmisc_1 @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X56))))
% 4.80/4.99          | ~ (v1_funct_2 @ X58 @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X56))
% 4.80/4.99          | ~ (v1_funct_1 @ X58)
% 4.80/4.99          | ~ (l1_pre_topc @ X57))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_7])).
% 4.80/4.99  thf('39', plain,
% 4.80/4.99      ((~ (l1_pre_topc @ sk_A)
% 4.80/4.99        | ~ (v1_funct_1 @ sk_C_1)
% 4.80/4.99        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.80/4.99             (u1_struct_0 @ sk_B_3))
% 4.80/4.99        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ~ (l1_pre_topc @ sk_B_3))),
% 4.80/4.99      inference('sup-', [status(thm)], ['37', '38'])).
% 4.80/4.99  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('41', plain, ((v1_funct_1 @ sk_C_1)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('42', plain,
% 4.80/4.99      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('43', plain, ((l1_pre_topc @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('44', plain,
% 4.80/4.99      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 4.80/4.99  thf('45', plain,
% 4.80/4.99      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('sup-', [status(thm)], ['36', '44'])).
% 4.80/4.99  thf('46', plain,
% 4.80/4.99      ((m1_subset_1 @ sk_C_1 @ 
% 4.80/4.99        (k1_zfmisc_1 @ 
% 4.80/4.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf(dt_k8_relset_1, axiom,
% 4.80/4.99    (![A:$i,B:$i,C:$i,D:$i]:
% 4.80/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/4.99       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.80/4.99  thf('47', plain,
% 4.80/4.99      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 4.80/4.99         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.80/4.99          | (m1_subset_1 @ (k8_relset_1 @ X28 @ X29 @ X27 @ X30) @ 
% 4.80/4.99             (k1_zfmisc_1 @ X28)))),
% 4.80/4.99      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 4.80/4.99  thf('48', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         (m1_subset_1 @ 
% 4.80/4.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.80/4.99           sk_C_1 @ X0) @ 
% 4.80/4.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['46', '47'])).
% 4.80/4.99  thf(t17_tdlat_3, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.80/4.99       ( ( v1_tdlat_3 @ A ) <=>
% 4.80/4.99         ( ![B:$i]:
% 4.80/4.99           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.80/4.99             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 4.80/4.99  thf('49', plain,
% 4.80/4.99      (![X64 : $i, X65 : $i]:
% 4.80/4.99         (~ (v1_tdlat_3 @ X64)
% 4.80/4.99          | (v3_pre_topc @ X65 @ X64)
% 4.80/4.99          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 4.80/4.99          | ~ (l1_pre_topc @ X64)
% 4.80/4.99          | ~ (v2_pre_topc @ X64))),
% 4.80/4.99      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 4.80/4.99  thf('50', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         (~ (v2_pre_topc @ sk_A)
% 4.80/4.99          | ~ (l1_pre_topc @ sk_A)
% 4.80/4.99          | (v3_pre_topc @ 
% 4.80/4.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.80/4.99              sk_C_1 @ X0) @ 
% 4.80/4.99             sk_A)
% 4.80/4.99          | ~ (v1_tdlat_3 @ sk_A))),
% 4.80/4.99      inference('sup-', [status(thm)], ['48', '49'])).
% 4.80/4.99  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('53', plain, ((v1_tdlat_3 @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('54', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         (v3_pre_topc @ 
% 4.80/4.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.80/4.99           sk_C_1 @ X0) @ 
% 4.80/4.99          sk_A)),
% 4.80/4.99      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 4.80/4.99  thf('55', plain,
% 4.80/4.99      (![X47 : $i, X48 : $i, X50 : $i, X51 : $i]:
% 4.80/4.99         ((zip_tseitin_1 @ X47 @ X50 @ X48 @ X51)
% 4.80/4.99          | ~ (v3_pre_topc @ 
% 4.80/4.99               (k8_relset_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X48) @ 
% 4.80/4.99                X50 @ X47) @ 
% 4.80/4.99               X51))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.80/4.99  thf('56', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 4.80/4.99      inference('sup-', [status(thm)], ['54', '55'])).
% 4.80/4.99  thf('57', plain,
% 4.80/4.99      (![X52 : $i, X53 : $i, X54 : $i]:
% 4.80/4.99         (~ (zip_tseitin_1 @ (sk_D @ X52 @ X53 @ X54) @ X54 @ X53 @ X52)
% 4.80/4.99          | (v5_pre_topc @ X54 @ X52 @ X53)
% 4.80/4.99          | ~ (zip_tseitin_2 @ X54 @ X53 @ X52))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.80/4.99  thf('58', plain,
% 4.80/4.99      ((~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.80/4.99        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3))),
% 4.80/4.99      inference('sup-', [status(thm)], ['56', '57'])).
% 4.80/4.99  thf('59', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('60', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 4.80/4.99      inference('clc', [status(thm)], ['58', '59'])).
% 4.80/4.99  thf('61', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['45', '60'])).
% 4.80/4.99  thf('62', plain, (~ (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 4.80/4.99      inference('demod', [status(thm)], ['0', '61'])).
% 4.80/4.99  thf('63', plain,
% 4.80/4.99      (![X45 : $i, X46 : $i]:
% 4.80/4.99         ((zip_tseitin_0 @ X45 @ X46) | ((k2_struct_0 @ X45) = (k1_xboole_0)))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/4.99  thf('64', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 4.80/4.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.80/4.99  thf('65', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.80/4.99         ((r1_tarski @ (k2_struct_0 @ X0) @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 4.80/4.99      inference('sup+', [status(thm)], ['63', '64'])).
% 4.80/4.99  thf('66', plain,
% 4.80/4.99      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 4.80/4.99  thf('67', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         ((r1_tarski @ (k2_struct_0 @ sk_B_3) @ X0)
% 4.80/4.99          | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('sup-', [status(thm)], ['65', '66'])).
% 4.80/4.99  thf('68', plain,
% 4.80/4.99      (![X41 : $i]:
% 4.80/4.99         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.80/4.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.80/4.99  thf('69', plain,
% 4.80/4.99      ((m1_subset_1 @ sk_C_1 @ 
% 4.80/4.99        (k1_zfmisc_1 @ 
% 4.80/4.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf(t56_tops_2, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.80/4.99       ( ![B:$i]:
% 4.80/4.99         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.80/4.99           ( ![C:$i]:
% 4.80/4.99             ( ( ( v1_funct_1 @ C ) & 
% 4.80/4.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.80/4.99                 ( m1_subset_1 @
% 4.80/4.99                   C @ 
% 4.80/4.99                   ( k1_zfmisc_1 @
% 4.80/4.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.80/4.99               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.80/4.99                 ( ![D:$i]:
% 4.80/4.99                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.80/4.99                     ( r1_tarski @
% 4.80/4.99                       ( k2_pre_topc @
% 4.80/4.99                         A @ 
% 4.80/4.99                         ( k8_relset_1 @
% 4.80/4.99                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 4.80/4.99                       ( k8_relset_1 @
% 4.80/4.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 4.80/4.99                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 4.80/4.99  thf('70', plain,
% 4.80/4.99      (![X59 : $i, X60 : $i, X61 : $i]:
% 4.80/4.99         (~ (v2_pre_topc @ X59)
% 4.80/4.99          | ~ (l1_pre_topc @ X59)
% 4.80/4.99          | (m1_subset_1 @ (sk_D_1 @ X60 @ X59 @ X61) @ 
% 4.80/4.99             (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 4.80/4.99          | (v5_pre_topc @ X60 @ X61 @ X59)
% 4.80/4.99          | ~ (m1_subset_1 @ X60 @ 
% 4.80/4.99               (k1_zfmisc_1 @ 
% 4.80/4.99                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X59))))
% 4.80/4.99          | ~ (v1_funct_2 @ X60 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X59))
% 4.80/4.99          | ~ (v1_funct_1 @ X60)
% 4.80/4.99          | ~ (l1_pre_topc @ X61)
% 4.80/4.99          | ~ (v2_pre_topc @ X61))),
% 4.80/4.99      inference('cnf', [status(esa)], [t56_tops_2])).
% 4.80/4.99  thf('71', plain,
% 4.80/4.99      ((~ (v2_pre_topc @ sk_A)
% 4.80/4.99        | ~ (l1_pre_topc @ sk_A)
% 4.80/4.99        | ~ (v1_funct_1 @ sk_C_1)
% 4.80/4.99        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.80/4.99             (u1_struct_0 @ sk_B_3))
% 4.80/4.99        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)
% 4.80/4.99        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.80/4.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))
% 4.80/4.99        | ~ (l1_pre_topc @ sk_B_3)
% 4.80/4.99        | ~ (v2_pre_topc @ sk_B_3))),
% 4.80/4.99      inference('sup-', [status(thm)], ['69', '70'])).
% 4.80/4.99  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('74', plain, ((v1_funct_1 @ sk_C_1)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('75', plain,
% 4.80/4.99      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('76', plain, ((l1_pre_topc @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('77', plain, ((v2_pre_topc @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('78', plain,
% 4.80/4.99      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)
% 4.80/4.99        | (m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.80/4.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3))))),
% 4.80/4.99      inference('demod', [status(thm)],
% 4.80/4.99                ['71', '72', '73', '74', '75', '76', '77'])).
% 4.80/4.99  thf('79', plain, (~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('80', plain,
% 4.80/4.99      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.80/4.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('clc', [status(thm)], ['78', '79'])).
% 4.80/4.99  thf('81', plain,
% 4.80/4.99      (![X16 : $i, X17 : $i]:
% 4.80/4.99         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 4.80/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.80/4.99  thf('82', plain,
% 4.80/4.99      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('sup-', [status(thm)], ['80', '81'])).
% 4.80/4.99  thf('83', plain,
% 4.80/4.99      (((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (k2_struct_0 @ sk_B_3))
% 4.80/4.99        | ~ (l1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('sup+', [status(thm)], ['68', '82'])).
% 4.80/4.99  thf('84', plain, ((l1_struct_0 @ sk_B_3)),
% 4.80/4.99      inference('sup-', [status(thm)], ['25', '26'])).
% 4.80/4.99  thf('85', plain,
% 4.80/4.99      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (k2_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('demod', [status(thm)], ['83', '84'])).
% 4.80/4.99  thf('86', plain,
% 4.80/4.99      (![X7 : $i, X9 : $i]:
% 4.80/4.99         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.80/4.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.80/4.99  thf('87', plain,
% 4.80/4.99      ((~ (r1_tarski @ (k2_struct_0 @ sk_B_3) @ 
% 4.80/4.99           (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A))
% 4.80/4.99        | ((k2_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['85', '86'])).
% 4.80/4.99  thf('88', plain,
% 4.80/4.99      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ((k2_struct_0 @ sk_B_3) = (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['67', '87'])).
% 4.80/4.99  thf('89', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['45', '60'])).
% 4.80/4.99  thf('90', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['45', '60'])).
% 4.80/4.99  thf('91', plain,
% 4.80/4.99      (((zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ((k2_struct_0 @ sk_B_3) = (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A)))),
% 4.80/4.99      inference('demod', [status(thm)], ['88', '89', '90'])).
% 4.80/4.99  thf('92', plain,
% 4.80/4.99      (![X45 : $i, X46 : $i]:
% 4.80/4.99         ((zip_tseitin_0 @ X45 @ X46) | ((k2_struct_0 @ X45) = (k1_xboole_0)))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.80/4.99  thf('93', plain,
% 4.80/4.99      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 4.80/4.99  thf('94', plain,
% 4.80/4.99      ((((k2_struct_0 @ sk_B_3) = (k1_xboole_0))
% 4.80/4.99        | (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('sup-', [status(thm)], ['92', '93'])).
% 4.80/4.99  thf('95', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['45', '60'])).
% 4.80/4.99  thf('96', plain,
% 4.80/4.99      ((((k2_struct_0 @ sk_B_3) = (k1_xboole_0))
% 4.80/4.99        | (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('demod', [status(thm)], ['94', '95'])).
% 4.80/4.99  thf('97', plain, (~ (zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)),
% 4.80/4.99      inference('clc', [status(thm)], ['58', '59'])).
% 4.80/4.99  thf('98', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['45', '60'])).
% 4.80/4.99  thf('99', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)),
% 4.80/4.99      inference('demod', [status(thm)], ['97', '98'])).
% 4.80/4.99  thf('100', plain, (((k2_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.80/4.99      inference('clc', [status(thm)], ['96', '99'])).
% 4.80/4.99  thf('101', plain,
% 4.80/4.99      (((zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A)))),
% 4.80/4.99      inference('demod', [status(thm)], ['91', '100'])).
% 4.80/4.99  thf('102', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)),
% 4.80/4.99      inference('demod', [status(thm)], ['97', '98'])).
% 4.80/4.99  thf('103', plain, (((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('clc', [status(thm)], ['101', '102'])).
% 4.80/4.99  thf('104', plain,
% 4.80/4.99      (![X59 : $i, X60 : $i, X61 : $i]:
% 4.80/4.99         (~ (v2_pre_topc @ X59)
% 4.80/4.99          | ~ (l1_pre_topc @ X59)
% 4.80/4.99          | ~ (r1_tarski @ 
% 4.80/4.99               (k2_pre_topc @ X61 @ 
% 4.80/4.99                (k8_relset_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X59) @ 
% 4.80/4.99                 X60 @ (sk_D_1 @ X60 @ X59 @ X61))) @ 
% 4.80/4.99               (k8_relset_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X59) @ 
% 4.80/4.99                X60 @ (k2_pre_topc @ X59 @ (sk_D_1 @ X60 @ X59 @ X61))))
% 4.80/4.99          | (v5_pre_topc @ X60 @ X61 @ X59)
% 4.80/4.99          | ~ (m1_subset_1 @ X60 @ 
% 4.80/4.99               (k1_zfmisc_1 @ 
% 4.80/4.99                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X59))))
% 4.80/4.99          | ~ (v1_funct_2 @ X60 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X59))
% 4.80/4.99          | ~ (v1_funct_1 @ X60)
% 4.80/4.99          | ~ (l1_pre_topc @ X61)
% 4.80/4.99          | ~ (v2_pre_topc @ X61))),
% 4.80/4.99      inference('cnf', [status(esa)], [t56_tops_2])).
% 4.80/4.99  thf('105', plain,
% 4.80/4.99      ((~ (r1_tarski @ 
% 4.80/4.99           (k2_pre_topc @ sk_A @ 
% 4.80/4.99            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.80/4.99             k1_xboole_0 @ (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))) @ 
% 4.80/4.99           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 4.80/4.99            k1_xboole_0 @ (k2_pre_topc @ sk_B_3 @ k1_xboole_0)))
% 4.80/4.99        | ~ (v2_pre_topc @ sk_A)
% 4.80/4.99        | ~ (l1_pre_topc @ sk_A)
% 4.80/4.99        | ~ (v1_funct_1 @ k1_xboole_0)
% 4.80/4.99        | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 4.80/4.99             (u1_struct_0 @ sk_B_3))
% 4.80/4.99        | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.80/4.99             (k1_zfmisc_1 @ 
% 4.80/4.99              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))
% 4.80/4.99        | (v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)
% 4.80/4.99        | ~ (l1_pre_topc @ sk_B_3)
% 4.80/4.99        | ~ (v2_pre_topc @ sk_B_3))),
% 4.80/4.99      inference('sup-', [status(thm)], ['103', '104'])).
% 4.80/4.99  thf('106', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 4.80/4.99      inference('sup+', [status(thm)], ['1', '2'])).
% 4.80/4.99  thf('107', plain,
% 4.80/4.99      (![X41 : $i]:
% 4.80/4.99         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.80/4.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.80/4.99  thf('108', plain,
% 4.80/4.99      ((r1_tarski @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('sup-', [status(thm)], ['80', '81'])).
% 4.80/4.99  thf('109', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['4', '5'])).
% 4.80/4.99  thf('110', plain,
% 4.80/4.99      (![X7 : $i, X9 : $i]:
% 4.80/4.99         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.80/4.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.80/4.99  thf('111', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['109', '110'])).
% 4.80/4.99  thf('112', plain,
% 4.80/4.99      ((((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3))
% 4.80/4.99        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['108', '111'])).
% 4.80/4.99  thf('113', plain,
% 4.80/4.99      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 4.80/4.99        | ~ (l1_struct_0 @ sk_B_3)
% 4.80/4.99        | ((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['107', '112'])).
% 4.80/4.99  thf('114', plain, ((l1_struct_0 @ sk_B_3)),
% 4.80/4.99      inference('sup-', [status(thm)], ['25', '26'])).
% 4.80/4.99  thf('115', plain,
% 4.80/4.99      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3))
% 4.80/4.99        | ((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('demod', [status(thm)], ['113', '114'])).
% 4.80/4.99  thf('116', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         ((zip_tseitin_0 @ sk_B_3 @ X0)
% 4.80/4.99          | ((sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) = (u1_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['106', '115'])).
% 4.80/4.99  thf('117', plain,
% 4.80/4.99      (![X41 : $i]:
% 4.80/4.99         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.80/4.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.80/4.99  thf('118', plain,
% 4.80/4.99      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.80/4.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('clc', [status(thm)], ['78', '79'])).
% 4.80/4.99  thf('119', plain,
% 4.80/4.99      (((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.80/4.99         (k1_zfmisc_1 @ (k2_struct_0 @ sk_B_3)))
% 4.80/4.99        | ~ (l1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('sup+', [status(thm)], ['117', '118'])).
% 4.80/4.99  thf('120', plain, ((l1_struct_0 @ sk_B_3)),
% 4.80/4.99      inference('sup-', [status(thm)], ['25', '26'])).
% 4.80/4.99  thf('121', plain,
% 4.80/4.99      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B_3 @ sk_A) @ 
% 4.80/4.99        (k1_zfmisc_1 @ (k2_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('demod', [status(thm)], ['119', '120'])).
% 4.80/4.99  thf('122', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         ((m1_subset_1 @ (u1_struct_0 @ sk_B_3) @ 
% 4.80/4.99           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B_3)))
% 4.80/4.99          | (zip_tseitin_0 @ sk_B_3 @ X0))),
% 4.80/4.99      inference('sup+', [status(thm)], ['116', '121'])).
% 4.80/4.99  thf('123', plain,
% 4.80/4.99      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['6', '9'])).
% 4.80/4.99  thf('124', plain,
% 4.80/4.99      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 4.80/4.99      inference('simplify', [status(thm)], ['11'])).
% 4.80/4.99  thf(cc4_relset_1, axiom,
% 4.80/4.99    (![A:$i,B:$i]:
% 4.80/4.99     ( ( v1_xboole_0 @ A ) =>
% 4.80/4.99       ( ![C:$i]:
% 4.80/4.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 4.80/4.99           ( v1_xboole_0 @ C ) ) ) ))).
% 4.80/4.99  thf('125', plain,
% 4.80/4.99      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X24)
% 4.80/4.99          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 4.80/4.99          | (v1_xboole_0 @ X25))),
% 4.80/4.99      inference('cnf', [status(esa)], [cc4_relset_1])).
% 4.80/4.99  thf('126', plain,
% 4.80/4.99      (![X1 : $i]:
% 4.80/4.99         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.80/4.99          | (v1_xboole_0 @ X1)
% 4.80/4.99          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['124', '125'])).
% 4.80/4.99  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.80/4.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.80/4.99  thf('128', plain,
% 4.80/4.99      (![X1 : $i]:
% 4.80/4.99         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.80/4.99          | (v1_xboole_0 @ X1))),
% 4.80/4.99      inference('demod', [status(thm)], ['126', '127'])).
% 4.80/4.99  thf('129', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 4.80/4.99          | ~ (v1_xboole_0 @ X0)
% 4.80/4.99          | (v1_xboole_0 @ X1))),
% 4.80/4.99      inference('sup-', [status(thm)], ['123', '128'])).
% 4.80/4.99  thf('130', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         ((zip_tseitin_0 @ sk_B_3 @ X0)
% 4.80/4.99          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 4.80/4.99          | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_B_3)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['122', '129'])).
% 4.80/4.99  thf('131', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         ((v1_xboole_0 @ (k2_struct_0 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 4.80/4.99      inference('sup+', [status(thm)], ['1', '2'])).
% 4.80/4.99  thf('132', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 4.80/4.99          | (zip_tseitin_0 @ sk_B_3 @ X0))),
% 4.80/4.99      inference('clc', [status(thm)], ['130', '131'])).
% 4.80/4.99  thf('133', plain,
% 4.80/4.99      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['6', '9'])).
% 4.80/4.99  thf('134', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         ((zip_tseitin_0 @ sk_B_3 @ X0)
% 4.80/4.99          | ((u1_struct_0 @ sk_B_3) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['132', '133'])).
% 4.80/4.99  thf('135', plain,
% 4.80/4.99      (((zip_tseitin_2 @ sk_C_1 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 4.80/4.99  thf('136', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['45', '60'])).
% 4.80/4.99  thf('137', plain,
% 4.80/4.99      (((zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)
% 4.80/4.99        | ~ (zip_tseitin_0 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('demod', [status(thm)], ['135', '136'])).
% 4.80/4.99  thf('138', plain, (~ (zip_tseitin_2 @ k1_xboole_0 @ sk_B_3 @ sk_A)),
% 4.80/4.99      inference('demod', [status(thm)], ['97', '98'])).
% 4.80/4.99  thf('139', plain, (~ (zip_tseitin_0 @ sk_B_3 @ sk_A)),
% 4.80/4.99      inference('clc', [status(thm)], ['137', '138'])).
% 4.80/4.99  thf('140', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['134', '139'])).
% 4.80/4.99  thf('141', plain, (((k1_xboole_0) = (sk_D_1 @ k1_xboole_0 @ sk_B_3 @ sk_A))),
% 4.80/4.99      inference('clc', [status(thm)], ['101', '102'])).
% 4.80/4.99  thf('142', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 4.80/4.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.80/4.99  thf('143', plain,
% 4.80/4.99      (![X16 : $i, X18 : $i]:
% 4.80/4.99         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 4.80/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.80/4.99  thf('144', plain,
% 4.80/4.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['142', '143'])).
% 4.80/4.99  thf(t38_relset_1, axiom,
% 4.80/4.99    (![A:$i,B:$i,C:$i]:
% 4.80/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/4.99       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 4.80/4.99         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.80/4.99  thf('145', plain,
% 4.80/4.99      (![X34 : $i, X35 : $i, X36 : $i]:
% 4.80/4.99         (((k8_relset_1 @ X34 @ X35 @ X36 @ X35)
% 4.80/4.99            = (k1_relset_1 @ X34 @ X35 @ X36))
% 4.80/4.99          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 4.80/4.99      inference('cnf', [status(esa)], [t38_relset_1])).
% 4.80/4.99  thf('146', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 4.80/4.99           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['144', '145'])).
% 4.80/4.99  thf('147', plain,
% 4.80/4.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['142', '143'])).
% 4.80/4.99  thf(redefinition_k1_relset_1, axiom,
% 4.80/4.99    (![A:$i,B:$i,C:$i]:
% 4.80/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/4.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.80/4.99  thf('148', plain,
% 4.80/4.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.80/4.99         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 4.80/4.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 4.80/4.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.80/4.99  thf('149', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['147', '148'])).
% 4.80/4.99  thf('150', plain,
% 4.80/4.99      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 4.80/4.99      inference('simplify', [status(thm)], ['11'])).
% 4.80/4.99  thf(dt_k6_partfun1, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( m1_subset_1 @
% 4.80/4.99         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.80/4.99       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.80/4.99  thf('151', plain,
% 4.80/4.99      (![X40 : $i]:
% 4.80/4.99         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 4.80/4.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 4.80/4.99      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.80/4.99  thf('152', plain,
% 4.80/4.99      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.80/4.99      inference('sup+', [status(thm)], ['150', '151'])).
% 4.80/4.99  thf('153', plain,
% 4.80/4.99      (![X16 : $i, X17 : $i]:
% 4.80/4.99         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 4.80/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.80/4.99  thf('154', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 4.80/4.99      inference('sup-', [status(thm)], ['152', '153'])).
% 4.80/4.99  thf('155', plain,
% 4.80/4.99      (![X7 : $i, X9 : $i]:
% 4.80/4.99         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.80/4.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.80/4.99  thf('156', plain,
% 4.80/4.99      ((~ (r1_tarski @ k1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))
% 4.80/4.99        | ((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['154', '155'])).
% 4.80/4.99  thf('157', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 4.80/4.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.80/4.99  thf('158', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 4.80/4.99      inference('demod', [status(thm)], ['156', '157'])).
% 4.80/4.99  thf('159', plain, (![X39 : $i]: (v1_partfun1 @ (k6_partfun1 @ X39) @ X39)),
% 4.80/4.99      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.80/4.99  thf('160', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 4.80/4.99      inference('sup+', [status(thm)], ['158', '159'])).
% 4.80/4.99  thf(d4_partfun1, axiom,
% 4.80/4.99    (![A:$i,B:$i]:
% 4.80/4.99     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.80/4.99       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 4.80/4.99  thf('161', plain,
% 4.80/4.99      (![X37 : $i, X38 : $i]:
% 4.80/4.99         (~ (v1_partfun1 @ X38 @ X37)
% 4.80/4.99          | ((k1_relat_1 @ X38) = (X37))
% 4.80/4.99          | ~ (v4_relat_1 @ X38 @ X37)
% 4.80/4.99          | ~ (v1_relat_1 @ X38))),
% 4.80/4.99      inference('cnf', [status(esa)], [d4_partfun1])).
% 4.80/4.99  thf('162', plain,
% 4.80/4.99      ((~ (v1_relat_1 @ k1_xboole_0)
% 4.80/4.99        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 4.80/4.99        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['160', '161'])).
% 4.80/4.99  thf('163', plain,
% 4.80/4.99      (![X12 : $i, X13 : $i]:
% 4.80/4.99         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 4.80/4.99          | ((X12) != (k1_xboole_0)))),
% 4.80/4.99      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.80/4.99  thf('164', plain,
% 4.80/4.99      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 4.80/4.99      inference('simplify', [status(thm)], ['163'])).
% 4.80/4.99  thf(fc6_relat_1, axiom,
% 4.80/4.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.80/4.99  thf('165', plain,
% 4.80/4.99      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 4.80/4.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.80/4.99  thf('166', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.80/4.99      inference('sup+', [status(thm)], ['164', '165'])).
% 4.80/4.99  thf('167', plain,
% 4.80/4.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['142', '143'])).
% 4.80/4.99  thf(cc2_relset_1, axiom,
% 4.80/4.99    (![A:$i,B:$i,C:$i]:
% 4.80/4.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.80/4.99       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.80/4.99  thf('168', plain,
% 4.80/4.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.80/4.99         ((v4_relat_1 @ X21 @ X22)
% 4.80/4.99          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.80/4.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.80/4.99  thf('169', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 4.80/4.99      inference('sup-', [status(thm)], ['167', '168'])).
% 4.80/4.99  thf('170', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.80/4.99      inference('demod', [status(thm)], ['162', '166', '169'])).
% 4.80/4.99  thf('171', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.80/4.99      inference('demod', [status(thm)], ['149', '170'])).
% 4.80/4.99  thf('172', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.80/4.99      inference('demod', [status(thm)], ['146', '171'])).
% 4.80/4.99  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('174', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['4', '5'])).
% 4.80/4.99  thf('175', plain,
% 4.80/4.99      (![X16 : $i, X18 : $i]:
% 4.80/4.99         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 4.80/4.99      inference('cnf', [status(esa)], [t3_subset])).
% 4.80/4.99  thf('176', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['174', '175'])).
% 4.80/4.99  thf(t18_tdlat_3, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.80/4.99       ( ( v1_tdlat_3 @ A ) <=>
% 4.80/4.99         ( ![B:$i]:
% 4.80/4.99           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.80/4.99             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 4.80/4.99  thf('177', plain,
% 4.80/4.99      (![X66 : $i, X67 : $i]:
% 4.80/4.99         (~ (v1_tdlat_3 @ X66)
% 4.80/4.99          | (v4_pre_topc @ X67 @ X66)
% 4.80/4.99          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 4.80/4.99          | ~ (l1_pre_topc @ X66)
% 4.80/4.99          | ~ (v2_pre_topc @ X66))),
% 4.80/4.99      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 4.80/4.99  thf('178', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X1)
% 4.80/4.99          | ~ (v2_pre_topc @ X0)
% 4.80/4.99          | ~ (l1_pre_topc @ X0)
% 4.80/4.99          | (v4_pre_topc @ X1 @ X0)
% 4.80/4.99          | ~ (v1_tdlat_3 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['176', '177'])).
% 4.80/4.99  thf('179', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         (~ (v1_tdlat_3 @ sk_A)
% 4.80/4.99          | (v4_pre_topc @ X0 @ sk_A)
% 4.80/4.99          | ~ (v2_pre_topc @ sk_A)
% 4.80/4.99          | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['173', '178'])).
% 4.80/4.99  thf('180', plain, ((v1_tdlat_3 @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('181', plain, ((v2_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('182', plain,
% 4.80/4.99      (![X0 : $i]: ((v4_pre_topc @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('demod', [status(thm)], ['179', '180', '181'])).
% 4.80/4.99  thf('183', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 4.80/4.99      inference('sup-', [status(thm)], ['174', '175'])).
% 4.80/4.99  thf(t52_pre_topc, axiom,
% 4.80/4.99    (![A:$i]:
% 4.80/4.99     ( ( l1_pre_topc @ A ) =>
% 4.80/4.99       ( ![B:$i]:
% 4.80/4.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.80/4.99           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 4.80/4.99             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 4.80/4.99               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 4.80/4.99  thf('184', plain,
% 4.80/4.99      (![X43 : $i, X44 : $i]:
% 4.80/4.99         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.80/4.99          | ~ (v4_pre_topc @ X43 @ X44)
% 4.80/4.99          | ((k2_pre_topc @ X44 @ X43) = (X43))
% 4.80/4.99          | ~ (l1_pre_topc @ X44))),
% 4.80/4.99      inference('cnf', [status(esa)], [t52_pre_topc])).
% 4.80/4.99  thf('185', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X1)
% 4.80/4.99          | ~ (l1_pre_topc @ X0)
% 4.80/4.99          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 4.80/4.99          | ~ (v4_pre_topc @ X1 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['183', '184'])).
% 4.80/4.99  thf('186', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X0)
% 4.80/4.99          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 4.80/4.99          | ~ (l1_pre_topc @ sk_A)
% 4.80/4.99          | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['182', '185'])).
% 4.80/4.99  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('188', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X0)
% 4.80/4.99          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 4.80/4.99          | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('demod', [status(thm)], ['186', '187'])).
% 4.80/4.99  thf('189', plain,
% 4.80/4.99      (![X0 : $i]: (((k2_pre_topc @ sk_A @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.80/4.99      inference('simplify', [status(thm)], ['188'])).
% 4.80/4.99  thf('190', plain,
% 4.80/4.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['142', '143'])).
% 4.80/4.99  thf('191', plain,
% 4.80/4.99      (![X43 : $i, X44 : $i]:
% 4.80/4.99         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.80/4.99          | ~ (v2_pre_topc @ X44)
% 4.80/4.99          | ((k2_pre_topc @ X44 @ X43) != (X43))
% 4.80/4.99          | (v4_pre_topc @ X43 @ X44)
% 4.80/4.99          | ~ (l1_pre_topc @ X44))),
% 4.80/4.99      inference('cnf', [status(esa)], [t52_pre_topc])).
% 4.80/4.99  thf('192', plain,
% 4.80/4.99      (![X0 : $i]:
% 4.80/4.99         (~ (l1_pre_topc @ X0)
% 4.80/4.99          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 4.80/4.99          | ((k2_pre_topc @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 4.80/4.99          | ~ (v2_pre_topc @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['190', '191'])).
% 4.80/4.99  thf('193', plain,
% 4.80/4.99      ((((k1_xboole_0) != (k1_xboole_0))
% 4.80/4.99        | ~ (v1_xboole_0 @ k1_xboole_0)
% 4.80/4.99        | ~ (v2_pre_topc @ sk_A)
% 4.80/4.99        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 4.80/4.99        | ~ (l1_pre_topc @ sk_A))),
% 4.80/4.99      inference('sup-', [status(thm)], ['189', '192'])).
% 4.80/4.99  thf('194', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.80/4.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.80/4.99  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('197', plain,
% 4.80/4.99      ((((k1_xboole_0) != (k1_xboole_0)) | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 4.80/4.99      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 4.80/4.99  thf('198', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 4.80/4.99      inference('simplify', [status(thm)], ['197'])).
% 4.80/4.99  thf('199', plain,
% 4.80/4.99      (![X0 : $i, X1 : $i]:
% 4.80/4.99         (~ (v1_xboole_0 @ X1)
% 4.80/4.99          | ~ (l1_pre_topc @ X0)
% 4.80/4.99          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 4.80/4.99          | ~ (v4_pre_topc @ X1 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['183', '184'])).
% 4.80/4.99  thf('200', plain,
% 4.80/4.99      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 4.80/4.99        | ~ (l1_pre_topc @ sk_A)
% 4.80/4.99        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['198', '199'])).
% 4.80/4.99  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('202', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.80/4.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.80/4.99  thf('203', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 4.80/4.99      inference('demod', [status(thm)], ['200', '201', '202'])).
% 4.80/4.99  thf('204', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['134', '139'])).
% 4.80/4.99  thf('205', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 4.80/4.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.80/4.99  thf('206', plain, ((v2_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('207', plain, ((l1_pre_topc @ sk_A)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('208', plain, ((v1_funct_1 @ sk_C_1)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('209', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['45', '60'])).
% 4.80/4.99  thf('210', plain, ((v1_funct_1 @ k1_xboole_0)),
% 4.80/4.99      inference('demod', [status(thm)], ['208', '209'])).
% 4.80/4.99  thf('211', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['134', '139'])).
% 4.80/4.99  thf('212', plain,
% 4.80/4.99      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('213', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['45', '60'])).
% 4.80/4.99  thf('214', plain,
% 4.80/4.99      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 4.80/4.99        (u1_struct_0 @ sk_B_3))),
% 4.80/4.99      inference('demod', [status(thm)], ['212', '213'])).
% 4.80/4.99  thf('215', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['134', '139'])).
% 4.80/4.99  thf('216', plain,
% 4.80/4.99      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 4.80/4.99      inference('demod', [status(thm)], ['214', '215'])).
% 4.80/4.99  thf('217', plain, (((u1_struct_0 @ sk_B_3) = (k1_xboole_0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['134', '139'])).
% 4.80/4.99  thf('218', plain,
% 4.80/4.99      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 4.80/4.99      inference('simplify', [status(thm)], ['11'])).
% 4.80/4.99  thf('219', plain,
% 4.80/4.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.80/4.99      inference('sup-', [status(thm)], ['142', '143'])).
% 4.80/4.99  thf('220', plain, ((l1_pre_topc @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('221', plain, ((v2_pre_topc @ sk_B_3)),
% 4.80/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/4.99  thf('222', plain, ((v5_pre_topc @ k1_xboole_0 @ sk_A @ sk_B_3)),
% 4.80/4.99      inference('demod', [status(thm)],
% 4.80/4.99                ['105', '140', '141', '172', '203', '204', '205', '206', 
% 4.80/4.99                 '207', '210', '211', '216', '217', '218', '219', '220', '221'])).
% 4.80/4.99  thf('223', plain, ($false), inference('demod', [status(thm)], ['62', '222'])).
% 4.80/4.99  
% 4.80/4.99  % SZS output end Refutation
% 4.80/4.99  
% 4.80/5.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
