%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBpQiSiByD

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:12 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 163 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  707 (2098 expanded)
%              Number of equality atoms :   38 ( 101 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k7_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k9_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X49: $i] :
      ( ( v1_funct_2 @ X49 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('4',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t44_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ X50 @ X51 @ X52 @ X53 ) @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','22','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','22','25'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X33 )
       != ( k1_tarski @ X32 ) )
      | ( ( k2_relat_1 @ X33 )
        = ( k1_tarski @ ( k1_funct_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X30: $i,X31: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','22','25'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k7_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k9_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBpQiSiByD
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:35:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 126 iterations in 0.227s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.67  thf(t3_funct_2, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ( v1_funct_1 @ A ) & 
% 0.47/0.67         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.47/0.67         ( m1_subset_1 @
% 0.47/0.67           A @ 
% 0.47/0.67           ( k1_zfmisc_1 @
% 0.47/0.67             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (![X49 : $i]:
% 0.47/0.67         ((m1_subset_1 @ X49 @ 
% 0.47/0.67           (k1_zfmisc_1 @ 
% 0.47/0.67            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))))
% 0.47/0.67          | ~ (v1_funct_1 @ X49)
% 0.47/0.67          | ~ (v1_relat_1 @ X49))),
% 0.47/0.67      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.67  thf(redefinition_k7_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.47/0.67          | ((k7_relset_1 @ X38 @ X39 @ X37 @ X40) = (k9_relat_1 @ X37 @ X40)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.47/0.67              = (k9_relat_1 @ X0 @ X1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (![X49 : $i]:
% 0.47/0.67         ((v1_funct_2 @ X49 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))
% 0.47/0.67          | ~ (v1_funct_1 @ X49)
% 0.47/0.67          | ~ (v1_relat_1 @ X49))),
% 0.47/0.67      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X49 : $i]:
% 0.47/0.67         ((m1_subset_1 @ X49 @ 
% 0.47/0.67           (k1_zfmisc_1 @ 
% 0.47/0.67            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))))
% 0.47/0.67          | ~ (v1_funct_1 @ X49)
% 0.47/0.67          | ~ (v1_relat_1 @ X49))),
% 0.47/0.67      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.67  thf(t44_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67       ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ))).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.47/0.67         ((r1_tarski @ (k7_relset_1 @ X50 @ X51 @ X52 @ X53) @ X51)
% 0.47/0.67          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.47/0.67          | ~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.47/0.67          | ~ (v1_funct_1 @ X52))),
% 0.47/0.67      inference('cnf', [status(esa)], [t44_funct_2])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.67          | (r1_tarski @ 
% 0.47/0.67             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.47/0.67             (k2_relat_1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ 
% 0.47/0.67           (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.47/0.67           (k2_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['6'])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | (r1_tarski @ 
% 0.47/0.67             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.47/0.67             (k2_relat_1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['3', '7'])).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ 
% 0.47/0.67           (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.47/0.67           (k2_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.47/0.67          | ~ (v1_funct_1 @ X1)
% 0.47/0.67          | ~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_funct_1 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['2', '9'])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_funct_1 @ X1)
% 0.47/0.67          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.67  thf(t64_funct_2, conjecture,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.67         ( m1_subset_1 @
% 0.47/0.67           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.67       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.67         ( r1_tarski @
% 0.47/0.67           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.67           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.67            ( m1_subset_1 @
% 0.47/0.67              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.67          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.67            ( r1_tarski @
% 0.47/0.67              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.67              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (~ (r1_tarski @ 
% 0.47/0.67          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.67          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('13', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(d1_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_1, axiom,
% 0.47/0.67    (![C:$i,B:$i,A:$i]:
% 0.47/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.47/0.67         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.47/0.67          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.47/0.67          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.47/0.67        | ((k1_tarski @ sk_A)
% 0.47/0.67            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.67  thf(zf_stmt_2, axiom,
% 0.47/0.67    (![B:$i,A:$i]:
% 0.47/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X41 : $i, X42 : $i]:
% 0.47/0.67         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_5, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.47/0.67         (~ (zip_tseitin_0 @ X46 @ X47)
% 0.47/0.67          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 0.47/0.67          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.47/0.67        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      ((((sk_B) = (k1_xboole_0))
% 0.47/0.67        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['16', '19'])).
% 0.47/0.67  thf('21', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('22', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.47/0.67          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.67  thf('26', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['15', '22', '25'])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (~ (r1_tarski @ 
% 0.47/0.67          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.67          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['12', '26'])).
% 0.47/0.67  thf('28', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['15', '22', '25'])).
% 0.47/0.67  thf(t14_funct_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.47/0.67         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      (![X32 : $i, X33 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X33) != (k1_tarski @ X32))
% 0.47/0.67          | ((k2_relat_1 @ X33) = (k1_tarski @ (k1_funct_1 @ X33 @ X32)))
% 0.47/0.67          | ~ (v1_funct_1 @ X33)
% 0.47/0.67          | ~ (v1_relat_1 @ X33))),
% 0.47/0.67      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.47/0.67        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.67        | ~ (v1_relat_1 @ sk_D))),
% 0.47/0.67      inference('eq_res', [status(thm)], ['30'])).
% 0.47/0.67  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc2_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (![X28 : $i, X29 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.47/0.67          | (v1_relat_1 @ X28)
% 0.47/0.67          | ~ (v1_relat_1 @ X29))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.47/0.67        | (v1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.67  thf(fc6_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      (![X30 : $i, X31 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X30 @ X31))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.67  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('demod', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['31', '32', '37'])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      (~ (r1_tarski @ 
% 0.47/0.67          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.67          (k2_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['27', '38'])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('41', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['15', '22', '25'])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.47/0.67      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.47/0.67          | ((k7_relset_1 @ X38 @ X39 @ X37 @ X40) = (k9_relat_1 @ X37 @ X40)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.47/0.67           = (k9_relat_1 @ sk_D @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['39', '44'])).
% 0.47/0.67  thf('46', plain, ((~ (v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['11', '45'])).
% 0.47/0.67  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('demod', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('49', plain, ($false),
% 0.47/0.67      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
