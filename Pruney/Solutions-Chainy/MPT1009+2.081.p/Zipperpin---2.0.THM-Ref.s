%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xy2lZ3FqXx

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:00 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 163 expanded)
%              Number of leaves         :   36 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  676 (2067 expanded)
%              Number of equality atoms :   40 ( 105 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X58 ) @ X59 )
      | ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X58 ) @ X59 ) ) )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k7_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k9_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X40 @ X41 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_funct_2 @ X54 @ X52 @ X53 )
      | ( X52
        = ( k1_relset_1 @ X52 @ X53 @ X54 ) )
      | ~ ( zip_tseitin_1 @ X54 @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X50: $i,X51: $i] :
      ( ( zip_tseitin_0 @ X50 @ X51 )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( zip_tseitin_0 @ X55 @ X56 )
      | ( zip_tseitin_1 @ X57 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relset_1 @ X44 @ X45 @ X43 )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ X35 )
       != ( k1_tarski @ X34 ) )
      | ( ( k2_relat_1 @ X35 )
        = ( k1_tarski @ ( k1_funct_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k7_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k9_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xy2lZ3FqXx
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.93  % Solved by: fo/fo7.sh
% 0.67/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.93  % done 245 iterations in 0.477s
% 0.67/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.93  % SZS output start Refutation
% 0.67/0.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.67/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.93  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.67/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.93  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.67/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.67/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.67/0.93  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.67/0.93  thf(sk_D_type, type, sk_D: $i).
% 0.67/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.93  thf(d10_xboole_0, axiom,
% 0.67/0.93    (![A:$i,B:$i]:
% 0.67/0.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.93  thf('0', plain,
% 0.67/0.93      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.67/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.93  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.67/0.93      inference('simplify', [status(thm)], ['0'])).
% 0.67/0.93  thf(t4_funct_2, axiom,
% 0.67/0.93    (![A:$i,B:$i]:
% 0.67/0.93     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.93       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.67/0.93         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.67/0.93           ( m1_subset_1 @
% 0.67/0.93             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.67/0.93  thf('2', plain,
% 0.67/0.93      (![X58 : $i, X59 : $i]:
% 0.67/0.93         (~ (r1_tarski @ (k2_relat_1 @ X58) @ X59)
% 0.67/0.93          | (m1_subset_1 @ X58 @ 
% 0.67/0.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X58) @ X59)))
% 0.67/0.93          | ~ (v1_funct_1 @ X58)
% 0.67/0.93          | ~ (v1_relat_1 @ X58))),
% 0.67/0.93      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.67/0.93  thf('3', plain,
% 0.67/0.93      (![X0 : $i]:
% 0.67/0.93         (~ (v1_relat_1 @ X0)
% 0.67/0.93          | ~ (v1_funct_1 @ X0)
% 0.67/0.93          | (m1_subset_1 @ X0 @ 
% 0.67/0.93             (k1_zfmisc_1 @ 
% 0.67/0.93              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.67/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.93  thf(redefinition_k7_relset_1, axiom,
% 0.67/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.93       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.67/0.93  thf('4', plain,
% 0.67/0.93      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.67/0.93         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.67/0.93          | ((k7_relset_1 @ X47 @ X48 @ X46 @ X49) = (k9_relat_1 @ X46 @ X49)))),
% 0.67/0.93      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.67/0.93  thf('5', plain,
% 0.67/0.93      (![X0 : $i, X1 : $i]:
% 0.67/0.93         (~ (v1_funct_1 @ X0)
% 0.67/0.93          | ~ (v1_relat_1 @ X0)
% 0.67/0.93          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.67/0.93              = (k9_relat_1 @ X0 @ X1)))),
% 0.67/0.93      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.93  thf('6', plain,
% 0.67/0.93      (![X0 : $i]:
% 0.67/0.93         (~ (v1_relat_1 @ X0)
% 0.67/0.93          | ~ (v1_funct_1 @ X0)
% 0.67/0.93          | (m1_subset_1 @ X0 @ 
% 0.67/0.93             (k1_zfmisc_1 @ 
% 0.67/0.93              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.67/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.93  thf(dt_k7_relset_1, axiom,
% 0.67/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.93       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.67/0.93  thf('7', plain,
% 0.67/0.93      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.67/0.93         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.67/0.93          | (m1_subset_1 @ (k7_relset_1 @ X40 @ X41 @ X39 @ X42) @ 
% 0.67/0.93             (k1_zfmisc_1 @ X41)))),
% 0.67/0.93      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.67/0.93  thf('8', plain,
% 0.67/0.93      (![X0 : $i, X1 : $i]:
% 0.67/0.93         (~ (v1_funct_1 @ X0)
% 0.67/0.93          | ~ (v1_relat_1 @ X0)
% 0.67/0.93          | (m1_subset_1 @ 
% 0.67/0.93             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.67/0.93             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 0.67/0.93      inference('sup-', [status(thm)], ['6', '7'])).
% 0.67/0.93  thf(t3_subset, axiom,
% 0.67/0.93    (![A:$i,B:$i]:
% 0.67/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.93  thf('9', plain,
% 0.67/0.93      (![X31 : $i, X32 : $i]:
% 0.67/0.93         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.67/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.93  thf('10', plain,
% 0.67/0.93      (![X0 : $i, X1 : $i]:
% 0.67/0.93         (~ (v1_relat_1 @ X0)
% 0.67/0.93          | ~ (v1_funct_1 @ X0)
% 0.67/0.93          | (r1_tarski @ 
% 0.67/0.93             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.67/0.93             (k2_relat_1 @ X0)))),
% 0.67/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.67/0.93  thf('11', plain,
% 0.67/0.93      (![X0 : $i, X1 : $i]:
% 0.67/0.93         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.67/0.93          | ~ (v1_relat_1 @ X1)
% 0.67/0.93          | ~ (v1_funct_1 @ X1)
% 0.67/0.93          | ~ (v1_funct_1 @ X1)
% 0.67/0.93          | ~ (v1_relat_1 @ X1))),
% 0.67/0.93      inference('sup+', [status(thm)], ['5', '10'])).
% 0.67/0.93  thf('12', plain,
% 0.67/0.93      (![X0 : $i, X1 : $i]:
% 0.67/0.93         (~ (v1_funct_1 @ X1)
% 0.67/0.93          | ~ (v1_relat_1 @ X1)
% 0.67/0.93          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.67/0.93      inference('simplify', [status(thm)], ['11'])).
% 0.67/0.93  thf(t64_funct_2, conjecture,
% 0.67/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.93     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.67/0.93         ( m1_subset_1 @
% 0.67/0.93           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.67/0.93       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.67/0.93         ( r1_tarski @
% 0.67/0.93           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.67/0.93           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.67/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.93    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.93        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.67/0.93            ( m1_subset_1 @
% 0.67/0.93              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.67/0.93          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.67/0.93            ( r1_tarski @
% 0.67/0.93              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.67/0.93              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.67/0.93    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.67/0.93  thf('13', plain,
% 0.67/0.93      (~ (r1_tarski @ 
% 0.67/0.93          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.67/0.93          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf('14', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf(d1_funct_2, axiom,
% 0.67/0.93    (![A:$i,B:$i,C:$i]:
% 0.67/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.67/0.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.67/0.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.67/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.67/0.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.67/0.93  thf(zf_stmt_1, axiom,
% 0.67/0.93    (![C:$i,B:$i,A:$i]:
% 0.67/0.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.67/0.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.67/0.93  thf('15', plain,
% 0.67/0.93      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.67/0.93         (~ (v1_funct_2 @ X54 @ X52 @ X53)
% 0.67/0.93          | ((X52) = (k1_relset_1 @ X52 @ X53 @ X54))
% 0.67/0.93          | ~ (zip_tseitin_1 @ X54 @ X53 @ X52))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.67/0.93  thf('16', plain,
% 0.67/0.93      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.67/0.93        | ((k1_tarski @ sk_A)
% 0.67/0.93            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.67/0.93      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.93  thf(zf_stmt_2, axiom,
% 0.67/0.93    (![B:$i,A:$i]:
% 0.67/0.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.93       ( zip_tseitin_0 @ B @ A ) ))).
% 0.67/0.93  thf('17', plain,
% 0.67/0.93      (![X50 : $i, X51 : $i]:
% 0.67/0.93         ((zip_tseitin_0 @ X50 @ X51) | ((X50) = (k1_xboole_0)))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.93  thf('18', plain,
% 0.67/0.93      ((m1_subset_1 @ sk_D @ 
% 0.67/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.67/0.93  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.67/0.93  thf(zf_stmt_5, axiom,
% 0.67/0.93    (![A:$i,B:$i,C:$i]:
% 0.67/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.67/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.67/0.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.67/0.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.67/0.93  thf('19', plain,
% 0.67/0.93      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.67/0.93         (~ (zip_tseitin_0 @ X55 @ X56)
% 0.67/0.93          | (zip_tseitin_1 @ X57 @ X55 @ X56)
% 0.67/0.93          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55))))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.67/0.93  thf('20', plain,
% 0.67/0.93      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.67/0.93        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.67/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.93  thf('21', plain,
% 0.67/0.93      ((((sk_B) = (k1_xboole_0))
% 0.67/0.93        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.67/0.93      inference('sup-', [status(thm)], ['17', '20'])).
% 0.67/0.93  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf('23', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.67/0.93      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.67/0.93  thf('24', plain,
% 0.67/0.93      ((m1_subset_1 @ sk_D @ 
% 0.67/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.67/0.93    (![A:$i,B:$i,C:$i]:
% 0.67/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.67/0.93  thf('25', plain,
% 0.67/0.93      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.67/0.93         (((k1_relset_1 @ X44 @ X45 @ X43) = (k1_relat_1 @ X43))
% 0.67/0.93          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.67/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.67/0.93  thf('26', plain,
% 0.67/0.93      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.67/0.93      inference('sup-', [status(thm)], ['24', '25'])).
% 0.67/0.93  thf('27', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.67/0.93      inference('demod', [status(thm)], ['16', '23', '26'])).
% 0.67/0.93  thf('28', plain,
% 0.67/0.93      (~ (r1_tarski @ 
% 0.67/0.93          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.67/0.93          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.67/0.93      inference('demod', [status(thm)], ['13', '27'])).
% 0.67/0.93  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.67/0.93      inference('demod', [status(thm)], ['16', '23', '26'])).
% 0.67/0.93  thf(t14_funct_1, axiom,
% 0.67/0.93    (![A:$i,B:$i]:
% 0.67/0.93     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.93       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.67/0.93         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.67/0.93  thf('30', plain,
% 0.67/0.93      (![X34 : $i, X35 : $i]:
% 0.67/0.93         (((k1_relat_1 @ X35) != (k1_tarski @ X34))
% 0.67/0.93          | ((k2_relat_1 @ X35) = (k1_tarski @ (k1_funct_1 @ X35 @ X34)))
% 0.67/0.93          | ~ (v1_funct_1 @ X35)
% 0.67/0.93          | ~ (v1_relat_1 @ X35))),
% 0.67/0.93      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.67/0.93  thf('31', plain,
% 0.67/0.93      (![X0 : $i]:
% 0.67/0.93         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.67/0.93          | ~ (v1_relat_1 @ X0)
% 0.67/0.93          | ~ (v1_funct_1 @ X0)
% 0.67/0.93          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.67/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.67/0.93  thf('32', plain,
% 0.67/0.93      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.67/0.93        | ~ (v1_funct_1 @ sk_D)
% 0.67/0.93        | ~ (v1_relat_1 @ sk_D))),
% 0.67/0.93      inference('eq_res', [status(thm)], ['31'])).
% 0.67/0.93  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf('34', plain,
% 0.67/0.93      ((m1_subset_1 @ sk_D @ 
% 0.67/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf(cc1_relset_1, axiom,
% 0.67/0.93    (![A:$i,B:$i,C:$i]:
% 0.67/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.93       ( v1_relat_1 @ C ) ))).
% 0.67/0.93  thf('35', plain,
% 0.67/0.93      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.67/0.93         ((v1_relat_1 @ X36)
% 0.67/0.93          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.67/0.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.93  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.67/0.93  thf('37', plain,
% 0.67/0.93      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.67/0.93      inference('demod', [status(thm)], ['32', '33', '36'])).
% 0.67/0.93  thf('38', plain,
% 0.67/0.93      (~ (r1_tarski @ 
% 0.67/0.93          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.67/0.93          (k2_relat_1 @ sk_D))),
% 0.67/0.93      inference('demod', [status(thm)], ['28', '37'])).
% 0.67/0.93  thf('39', plain,
% 0.67/0.93      ((m1_subset_1 @ sk_D @ 
% 0.67/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf('40', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.67/0.93      inference('demod', [status(thm)], ['16', '23', '26'])).
% 0.67/0.93  thf('41', plain,
% 0.67/0.93      ((m1_subset_1 @ sk_D @ 
% 0.67/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.67/0.93      inference('demod', [status(thm)], ['39', '40'])).
% 0.67/0.93  thf('42', plain,
% 0.67/0.93      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.67/0.93         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.67/0.93          | ((k7_relset_1 @ X47 @ X48 @ X46 @ X49) = (k9_relat_1 @ X46 @ X49)))),
% 0.67/0.93      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.67/0.93  thf('43', plain,
% 0.67/0.93      (![X0 : $i]:
% 0.67/0.93         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.67/0.93           = (k9_relat_1 @ sk_D @ X0))),
% 0.67/0.93      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.93  thf('44', plain,
% 0.67/0.93      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.67/0.93      inference('demod', [status(thm)], ['38', '43'])).
% 0.67/0.93  thf('45', plain, ((~ (v1_relat_1 @ sk_D) | ~ (v1_funct_1 @ sk_D))),
% 0.67/0.93      inference('sup-', [status(thm)], ['12', '44'])).
% 0.67/0.93  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.67/0.93  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.93  thf('48', plain, ($false),
% 0.67/0.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.67/0.93  
% 0.67/0.93  % SZS output end Refutation
% 0.67/0.93  
% 0.78/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
