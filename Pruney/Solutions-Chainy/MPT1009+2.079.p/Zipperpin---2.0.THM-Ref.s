%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bu2D7Ok82x

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:00 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 168 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  665 (2041 expanded)
%              Number of equality atoms :   40 ( 107 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X50 ) @ X51 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X52 )
      | ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k7_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k9_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X40 @ X41 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ( X55
        = ( k1_relset_1 @ X55 @ X56 @ X57 ) )
      | ~ ( zip_tseitin_1 @ X57 @ X56 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_0 @ X53 @ X54 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( zip_tseitin_0 @ X58 @ X59 )
      | ( zip_tseitin_1 @ X60 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relset_1 @ X44 @ X45 @ X43 )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ X35 )
       != ( k1_tarski @ X34 ) )
      | ( ( k2_relat_1 @ X35 )
        = ( k1_tarski @ ( k1_funct_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k7_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k9_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bu2D7Ok82x
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:37:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 179 iterations in 0.320s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.78  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.60/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.78  thf(d10_xboole_0, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.78  thf('0', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.60/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.78  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.78      inference('simplify', [status(thm)], ['0'])).
% 0.60/0.78  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.78      inference('simplify', [status(thm)], ['0'])).
% 0.60/0.78  thf(t11_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ C ) =>
% 0.60/0.78       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.60/0.78           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.60/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.60/0.78  thf('3', plain,
% 0.60/0.78      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.60/0.78         (~ (r1_tarski @ (k1_relat_1 @ X50) @ X51)
% 0.60/0.78          | ~ (r1_tarski @ (k2_relat_1 @ X50) @ X52)
% 0.60/0.78          | (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.60/0.78          | ~ (v1_relat_1 @ X50))),
% 0.60/0.78      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.60/0.78  thf('4', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X0)
% 0.60/0.78          | (m1_subset_1 @ X0 @ 
% 0.60/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.60/0.78          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.78  thf('5', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((m1_subset_1 @ X0 @ 
% 0.60/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.60/0.78          | ~ (v1_relat_1 @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['1', '4'])).
% 0.60/0.78  thf(redefinition_k7_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.60/0.78          | ((k7_relset_1 @ X47 @ X48 @ X46 @ X49) = (k9_relat_1 @ X46 @ X49)))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.60/0.78  thf('7', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X0)
% 0.60/0.78          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.60/0.78              = (k9_relat_1 @ X0 @ X1)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.78  thf('8', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((m1_subset_1 @ X0 @ 
% 0.60/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.60/0.78          | ~ (v1_relat_1 @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['1', '4'])).
% 0.60/0.78  thf(dt_k7_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.60/0.78  thf('9', plain,
% 0.60/0.78      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.60/0.78          | (m1_subset_1 @ (k7_relset_1 @ X40 @ X41 @ X39 @ X42) @ 
% 0.60/0.78             (k1_zfmisc_1 @ X41)))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.60/0.78  thf('10', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X0)
% 0.60/0.78          | (m1_subset_1 @ 
% 0.60/0.78             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.60/0.78             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['8', '9'])).
% 0.60/0.78  thf('11', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.60/0.78           (k1_zfmisc_1 @ (k2_relat_1 @ X1)))
% 0.60/0.78          | ~ (v1_relat_1 @ X1)
% 0.60/0.78          | ~ (v1_relat_1 @ X1))),
% 0.60/0.78      inference('sup+', [status(thm)], ['7', '10'])).
% 0.60/0.78  thf('12', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X1)
% 0.60/0.78          | (m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.60/0.78             (k1_zfmisc_1 @ (k2_relat_1 @ X1))))),
% 0.60/0.78      inference('simplify', [status(thm)], ['11'])).
% 0.60/0.78  thf(t3_subset, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.78  thf('13', plain,
% 0.60/0.78      (![X31 : $i, X32 : $i]:
% 0.60/0.78         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.78  thf('14', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X0)
% 0.60/0.78          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.78  thf(t64_funct_2, conjecture,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.60/0.78         ( m1_subset_1 @
% 0.60/0.78           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.60/0.78       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.60/0.78         ( r1_tarski @
% 0.60/0.78           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.60/0.78           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.60/0.78            ( m1_subset_1 @
% 0.60/0.78              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.60/0.78          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.60/0.78            ( r1_tarski @
% 0.60/0.78              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.60/0.78              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.60/0.78  thf('15', plain,
% 0.60/0.78      (~ (r1_tarski @ 
% 0.60/0.78          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.60/0.78          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('16', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(d1_funct_2, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_1, axiom,
% 0.60/0.78    (![C:$i,B:$i,A:$i]:
% 0.60/0.78     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.78  thf('17', plain,
% 0.60/0.78      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.60/0.78         (~ (v1_funct_2 @ X57 @ X55 @ X56)
% 0.60/0.78          | ((X55) = (k1_relset_1 @ X55 @ X56 @ X57))
% 0.60/0.78          | ~ (zip_tseitin_1 @ X57 @ X56 @ X55))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.78  thf('18', plain,
% 0.60/0.78      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.60/0.78        | ((k1_tarski @ sk_A)
% 0.60/0.78            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.78  thf(zf_stmt_2, axiom,
% 0.60/0.78    (![B:$i,A:$i]:
% 0.60/0.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.78       ( zip_tseitin_0 @ B @ A ) ))).
% 0.60/0.78  thf('19', plain,
% 0.60/0.78      (![X53 : $i, X54 : $i]:
% 0.60/0.78         ((zip_tseitin_0 @ X53 @ X54) | ((X53) = (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.78  thf('20', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_5, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.78  thf('21', plain,
% 0.60/0.78      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.60/0.78         (~ (zip_tseitin_0 @ X58 @ X59)
% 0.60/0.78          | (zip_tseitin_1 @ X60 @ X58 @ X59)
% 0.60/0.78          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.78  thf('22', plain,
% 0.60/0.78      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.60/0.78        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.78  thf('23', plain,
% 0.60/0.78      ((((sk_B) = (k1_xboole_0))
% 0.60/0.78        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['19', '22'])).
% 0.60/0.78  thf('24', plain, (((sk_B) != (k1_xboole_0))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('25', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.60/0.78      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.60/0.78  thf('26', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.78  thf('27', plain,
% 0.60/0.78      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.60/0.78         (((k1_relset_1 @ X44 @ X45 @ X43) = (k1_relat_1 @ X43))
% 0.60/0.78          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.78  thf('28', plain,
% 0.60/0.78      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.78  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['18', '25', '28'])).
% 0.60/0.78  thf('30', plain,
% 0.60/0.78      (~ (r1_tarski @ 
% 0.60/0.78          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.60/0.78          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.78      inference('demod', [status(thm)], ['15', '29'])).
% 0.60/0.78  thf('31', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['18', '25', '28'])).
% 0.60/0.78  thf(t14_funct_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.78       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.60/0.78         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.60/0.78  thf('32', plain,
% 0.60/0.78      (![X34 : $i, X35 : $i]:
% 0.60/0.78         (((k1_relat_1 @ X35) != (k1_tarski @ X34))
% 0.60/0.78          | ((k2_relat_1 @ X35) = (k1_tarski @ (k1_funct_1 @ X35 @ X34)))
% 0.60/0.78          | ~ (v1_funct_1 @ X35)
% 0.60/0.78          | ~ (v1_relat_1 @ X35))),
% 0.60/0.78      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.60/0.78  thf('33', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.60/0.78          | ~ (v1_relat_1 @ X0)
% 0.60/0.78          | ~ (v1_funct_1 @ X0)
% 0.60/0.78          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.78  thf('34', plain,
% 0.60/0.78      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.60/0.78        | ~ (v1_funct_1 @ sk_D)
% 0.60/0.78        | ~ (v1_relat_1 @ sk_D))),
% 0.60/0.78      inference('eq_res', [status(thm)], ['33'])).
% 0.60/0.78  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('36', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(cc1_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( v1_relat_1 @ C ) ))).
% 0.60/0.78  thf('37', plain,
% 0.60/0.78      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.60/0.78         ((v1_relat_1 @ X36)
% 0.60/0.78          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.78  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.78  thf('39', plain,
% 0.60/0.78      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.78      inference('demod', [status(thm)], ['34', '35', '38'])).
% 0.60/0.78  thf('40', plain,
% 0.60/0.78      (~ (r1_tarski @ 
% 0.60/0.78          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.60/0.78          (k2_relat_1 @ sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['30', '39'])).
% 0.60/0.78  thf('41', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('42', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['18', '25', '28'])).
% 0.60/0.78  thf('43', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.60/0.78      inference('demod', [status(thm)], ['41', '42'])).
% 0.60/0.78  thf('44', plain,
% 0.60/0.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.60/0.78          | ((k7_relset_1 @ X47 @ X48 @ X46 @ X49) = (k9_relat_1 @ X46 @ X49)))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.60/0.78  thf('45', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.60/0.78           = (k9_relat_1 @ sk_D @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['43', '44'])).
% 0.60/0.78  thf('46', plain,
% 0.60/0.78      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['40', '45'])).
% 0.60/0.78  thf('47', plain, (~ (v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['14', '46'])).
% 0.60/0.78  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.78  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.60/0.78  
% 0.60/0.78  % SZS output end Refutation
% 0.60/0.78  
% 0.60/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
