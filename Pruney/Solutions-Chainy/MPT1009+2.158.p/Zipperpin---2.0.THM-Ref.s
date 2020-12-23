%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WDHZnv2iAH

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:11 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 161 expanded)
%              Number of leaves         :   36 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  656 (2027 expanded)
%              Number of equality atoms :   38 ( 101 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k7_relset_1 @ X45 @ X46 @ X44 @ X47 )
        = ( k9_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

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

thf('10',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ( X50
        = ( k1_relset_1 @ X50 @ X51 @ X52 ) )
      | ~ ( zip_tseitin_1 @ X52 @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X48: $i,X49: $i] :
      ( ( zip_tseitin_0 @ X48 @ X49 )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( zip_tseitin_0 @ X53 @ X54 )
      | ( zip_tseitin_1 @ X55 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X41 )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relat_1 @ X36 )
       != ( k1_tarski @ X35 ) )
      | ( ( k2_relat_1 @ X36 )
        = ( k1_tarski @ ( k1_funct_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k7_relset_1 @ X45 @ X46 @ X44 @ X47 )
        = ( k9_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WDHZnv2iAH
% 0.14/0.37  % Computer   : n008.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 18:34:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 128 iterations in 0.181s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(t3_funct_2, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.63       ( ( v1_funct_1 @ A ) & 
% 0.45/0.63         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.63         ( m1_subset_1 @
% 0.45/0.63           A @ 
% 0.45/0.63           ( k1_zfmisc_1 @
% 0.45/0.63             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (![X56 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X56 @ 
% 0.45/0.63           (k1_zfmisc_1 @ 
% 0.45/0.63            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 0.45/0.63          | ~ (v1_funct_1 @ X56)
% 0.45/0.63          | ~ (v1_relat_1 @ X56))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.45/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.45/0.63          | ((k7_relset_1 @ X45 @ X46 @ X44 @ X47) = (k9_relat_1 @ X44 @ X47)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.45/0.63              = (k9_relat_1 @ X0 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X56 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X56 @ 
% 0.45/0.63           (k1_zfmisc_1 @ 
% 0.45/0.63            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 0.45/0.63          | ~ (v1_funct_1 @ X56)
% 0.45/0.63          | ~ (v1_relat_1 @ X56))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.45/0.63  thf(dt_k7_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.45/0.63          | (m1_subset_1 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X40) @ 
% 0.45/0.63             (k1_zfmisc_1 @ X39)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | (m1_subset_1 @ 
% 0.45/0.63             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.45/0.63             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf(t3_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X28 : $i, X29 : $i]:
% 0.45/0.63         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | (r1_tarski @ 
% 0.45/0.63             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.45/0.63             (k2_relat_1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.45/0.63          | ~ (v1_funct_1 @ X1)
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | ~ (v1_funct_1 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['2', '7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X1)
% 0.45/0.63          | ~ (v1_funct_1 @ X1)
% 0.45/0.63          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['8'])).
% 0.45/0.63  thf(t64_funct_2, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.63         ( m1_subset_1 @
% 0.45/0.63           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.63       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.63         ( r1_tarski @
% 0.45/0.63           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.63           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.63            ( m1_subset_1 @
% 0.45/0.63              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.63          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.63            ( r1_tarski @
% 0.45/0.63              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.63              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (~ (r1_tarski @ 
% 0.45/0.63          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.45/0.63          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('11', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d1_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_1, axiom,
% 0.45/0.63    (![C:$i,B:$i,A:$i]:
% 0.45/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.45/0.63         (~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.45/0.63          | ((X50) = (k1_relset_1 @ X50 @ X51 @ X52))
% 0.45/0.63          | ~ (zip_tseitin_1 @ X52 @ X51 @ X50))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.63        | ((k1_tarski @ sk_A)
% 0.45/0.63            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf(zf_stmt_2, axiom,
% 0.45/0.63    (![B:$i,A:$i]:
% 0.45/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X48 : $i, X49 : $i]:
% 0.45/0.63         ((zip_tseitin_0 @ X48 @ X49) | ((X48) = (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.63  thf(zf_stmt_5, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.45/0.63         (~ (zip_tseitin_0 @ X53 @ X54)
% 0.45/0.63          | (zip_tseitin_1 @ X55 @ X53 @ X54)
% 0.45/0.63          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.63        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      ((((sk_B) = (k1_xboole_0))
% 0.45/0.63        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.63  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('20', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.45/0.63         (((k1_relset_1 @ X42 @ X43 @ X41) = (k1_relat_1 @ X41))
% 0.45/0.63          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.63  thf('24', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (~ (r1_tarski @ 
% 0.45/0.63          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.45/0.63          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['10', '24'])).
% 0.45/0.63  thf('26', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.45/0.63  thf(t14_funct_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.63       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.45/0.63         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (![X35 : $i, X36 : $i]:
% 0.45/0.63         (((k1_relat_1 @ X36) != (k1_tarski @ X35))
% 0.45/0.63          | ((k2_relat_1 @ X36) = (k1_tarski @ (k1_funct_1 @ X36 @ X35)))
% 0.45/0.63          | ~ (v1_funct_1 @ X36)
% 0.45/0.63          | ~ (v1_relat_1 @ X36))),
% 0.45/0.63      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.45/0.63        | ~ (v1_funct_1 @ sk_D)
% 0.45/0.63        | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.63      inference('eq_res', [status(thm)], ['28'])).
% 0.45/0.63  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X31 : $i, X32 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.45/0.63          | (v1_relat_1 @ X31)
% 0.45/0.63          | ~ (v1_relat_1 @ X32))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.45/0.63        | (v1_relat_1 @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.63  thf(fc6_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.63  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['29', '30', '35'])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (~ (r1_tarski @ 
% 0.45/0.63          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.45/0.63          (k2_relat_1 @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['25', '36'])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('39', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.45/0.63          | ((k7_relset_1 @ X45 @ X46 @ X44 @ X47) = (k9_relat_1 @ X44 @ X47)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.45/0.63           = (k9_relat_1 @ sk_D @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['37', '42'])).
% 0.45/0.63  thf('44', plain, ((~ (v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['9', '43'])).
% 0.45/0.63  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.63  thf('47', plain, ($false),
% 0.45/0.63      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
