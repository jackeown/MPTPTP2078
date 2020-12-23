%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nGuR94zlKO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:10 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 174 expanded)
%              Number of leaves         :   37 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  680 (2071 expanded)
%              Number of equality atoms :   40 ( 107 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X51 ) @ X53 )
      | ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k7_relset_1 @ X48 @ X49 @ X47 @ X50 )
        = ( k9_relat_1 @ X47 @ X50 ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 ) @ ( k1_zfmisc_1 @ X42 ) ) ) ),
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
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_2 @ X58 @ X56 @ X57 )
      | ( X56
        = ( k1_relset_1 @ X56 @ X57 @ X58 ) )
      | ~ ( zip_tseitin_1 @ X58 @ X57 @ X56 ) ) ),
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
    ! [X54: $i,X55: $i] :
      ( ( zip_tseitin_0 @ X54 @ X55 )
      | ( X54 = k1_xboole_0 ) ) ),
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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( zip_tseitin_0 @ X59 @ X60 )
      | ( zip_tseitin_1 @ X61 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X46 @ X44 )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( ( k1_relat_1 @ X39 )
       != ( k1_tarski @ X38 ) )
      | ( ( k2_relat_1 @ X39 )
        = ( k1_tarski @ ( k1_funct_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_relat_1 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X36: $i,X37: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k7_relset_1 @ X48 @ X49 @ X47 @ X50 )
        = ( k9_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nGuR94zlKO
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.57/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.80  % Solved by: fo/fo7.sh
% 0.57/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.80  % done 189 iterations in 0.333s
% 0.57/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.80  % SZS output start Refutation
% 0.57/0.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.57/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.80  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.57/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.57/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.80  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.57/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.57/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.57/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.80  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.57/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.57/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.80  thf(d10_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.80  thf('0', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.57/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.80  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.57/0.80      inference('simplify', [status(thm)], ['0'])).
% 0.57/0.80  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.57/0.80      inference('simplify', [status(thm)], ['0'])).
% 0.57/0.80  thf(t11_relset_1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( v1_relat_1 @ C ) =>
% 0.57/0.80       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.57/0.80           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.57/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.57/0.80  thf('3', plain,
% 0.57/0.80      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.57/0.80         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 0.57/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X51) @ X53)
% 0.57/0.80          | (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 0.57/0.80          | ~ (v1_relat_1 @ X51))),
% 0.57/0.80      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.57/0.80  thf('4', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_relat_1 @ X0)
% 0.57/0.80          | (m1_subset_1 @ X0 @ 
% 0.57/0.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.57/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.80  thf('5', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((m1_subset_1 @ X0 @ 
% 0.57/0.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.57/0.80          | ~ (v1_relat_1 @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['1', '4'])).
% 0.57/0.80  thf(redefinition_k7_relset_1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.57/0.80  thf('6', plain,
% 0.57/0.80      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.57/0.80         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.57/0.80          | ((k7_relset_1 @ X48 @ X49 @ X47 @ X50) = (k9_relat_1 @ X47 @ X50)))),
% 0.57/0.80      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.57/0.80  thf('7', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_relat_1 @ X0)
% 0.57/0.80          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.57/0.80              = (k9_relat_1 @ X0 @ X1)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.80  thf('8', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((m1_subset_1 @ X0 @ 
% 0.57/0.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.57/0.80          | ~ (v1_relat_1 @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['1', '4'])).
% 0.57/0.80  thf(dt_k7_relset_1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.57/0.80  thf('9', plain,
% 0.57/0.80      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.57/0.80         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.57/0.80          | (m1_subset_1 @ (k7_relset_1 @ X41 @ X42 @ X40 @ X43) @ 
% 0.57/0.80             (k1_zfmisc_1 @ X42)))),
% 0.57/0.80      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.57/0.80  thf('10', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_relat_1 @ X0)
% 0.57/0.80          | (m1_subset_1 @ 
% 0.57/0.80             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.57/0.80             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 0.57/0.80      inference('sup-', [status(thm)], ['8', '9'])).
% 0.57/0.80  thf('11', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.57/0.80           (k1_zfmisc_1 @ (k2_relat_1 @ X1)))
% 0.57/0.80          | ~ (v1_relat_1 @ X1)
% 0.57/0.80          | ~ (v1_relat_1 @ X1))),
% 0.57/0.80      inference('sup+', [status(thm)], ['7', '10'])).
% 0.57/0.80  thf('12', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_relat_1 @ X1)
% 0.57/0.80          | (m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.57/0.80             (k1_zfmisc_1 @ (k2_relat_1 @ X1))))),
% 0.57/0.80      inference('simplify', [status(thm)], ['11'])).
% 0.57/0.80  thf(t3_subset, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.80  thf('13', plain,
% 0.57/0.80      (![X31 : $i, X32 : $i]:
% 0.57/0.80         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.80  thf('14', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_relat_1 @ X0)
% 0.57/0.80          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.57/0.80  thf(t64_funct_2, conjecture,
% 0.57/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.80     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.57/0.80         ( m1_subset_1 @
% 0.57/0.80           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.57/0.80       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.57/0.80         ( r1_tarski @
% 0.57/0.80           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.57/0.80           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.57/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.80        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.57/0.80            ( m1_subset_1 @
% 0.57/0.80              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.57/0.80          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.57/0.80            ( r1_tarski @
% 0.57/0.80              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.57/0.80              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.57/0.80    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.57/0.80  thf('15', plain,
% 0.57/0.80      (~ (r1_tarski @ 
% 0.57/0.80          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.57/0.80          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('16', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf(d1_funct_2, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.57/0.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.57/0.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.57/0.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.57/0.80  thf(zf_stmt_1, axiom,
% 0.57/0.80    (![C:$i,B:$i,A:$i]:
% 0.57/0.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.57/0.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.57/0.80  thf('17', plain,
% 0.57/0.80      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.57/0.80         (~ (v1_funct_2 @ X58 @ X56 @ X57)
% 0.57/0.80          | ((X56) = (k1_relset_1 @ X56 @ X57 @ X58))
% 0.57/0.80          | ~ (zip_tseitin_1 @ X58 @ X57 @ X56))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.80  thf('18', plain,
% 0.57/0.80      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.57/0.80        | ((k1_tarski @ sk_A)
% 0.57/0.80            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.57/0.80  thf(zf_stmt_2, axiom,
% 0.57/0.80    (![B:$i,A:$i]:
% 0.57/0.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.80       ( zip_tseitin_0 @ B @ A ) ))).
% 0.57/0.80  thf('19', plain,
% 0.57/0.80      (![X54 : $i, X55 : $i]:
% 0.57/0.80         ((zip_tseitin_0 @ X54 @ X55) | ((X54) = (k1_xboole_0)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.80  thf('20', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_D @ 
% 0.57/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.57/0.80  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.57/0.80  thf(zf_stmt_5, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.57/0.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.57/0.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.57/0.80  thf('21', plain,
% 0.57/0.80      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.57/0.80         (~ (zip_tseitin_0 @ X59 @ X60)
% 0.57/0.80          | (zip_tseitin_1 @ X61 @ X59 @ X60)
% 0.57/0.80          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59))))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.57/0.80  thf('22', plain,
% 0.57/0.80      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.57/0.80        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['20', '21'])).
% 0.57/0.80  thf('23', plain,
% 0.57/0.80      ((((sk_B) = (k1_xboole_0))
% 0.57/0.80        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['19', '22'])).
% 0.57/0.80  thf('24', plain, (((sk_B) != (k1_xboole_0))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('25', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.57/0.80      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.57/0.80  thf('26', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_D @ 
% 0.57/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf(redefinition_k1_relset_1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.57/0.80  thf('27', plain,
% 0.57/0.80      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.57/0.80         (((k1_relset_1 @ X45 @ X46 @ X44) = (k1_relat_1 @ X44))
% 0.57/0.80          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.57/0.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.57/0.80  thf('28', plain,
% 0.57/0.80      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.57/0.80      inference('sup-', [status(thm)], ['26', '27'])).
% 0.57/0.80  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.57/0.80      inference('demod', [status(thm)], ['18', '25', '28'])).
% 0.57/0.80  thf('30', plain,
% 0.57/0.80      (~ (r1_tarski @ 
% 0.57/0.80          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.57/0.80          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.57/0.80      inference('demod', [status(thm)], ['15', '29'])).
% 0.57/0.80  thf('31', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.57/0.80      inference('demod', [status(thm)], ['18', '25', '28'])).
% 0.57/0.80  thf(t14_funct_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.57/0.80       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.57/0.80         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.57/0.80  thf('32', plain,
% 0.57/0.80      (![X38 : $i, X39 : $i]:
% 0.57/0.80         (((k1_relat_1 @ X39) != (k1_tarski @ X38))
% 0.57/0.80          | ((k2_relat_1 @ X39) = (k1_tarski @ (k1_funct_1 @ X39 @ X38)))
% 0.57/0.80          | ~ (v1_funct_1 @ X39)
% 0.57/0.80          | ~ (v1_relat_1 @ X39))),
% 0.57/0.80      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.57/0.80  thf('33', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.57/0.80          | ~ (v1_relat_1 @ X0)
% 0.57/0.80          | ~ (v1_funct_1 @ X0)
% 0.57/0.80          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.57/0.80      inference('sup-', [status(thm)], ['31', '32'])).
% 0.57/0.80  thf('34', plain,
% 0.57/0.80      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.57/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.57/0.80        | ~ (v1_relat_1 @ sk_D))),
% 0.57/0.80      inference('eq_res', [status(thm)], ['33'])).
% 0.57/0.80  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('36', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_D @ 
% 0.57/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf(cc2_relat_1, axiom,
% 0.57/0.80    (![A:$i]:
% 0.57/0.80     ( ( v1_relat_1 @ A ) =>
% 0.57/0.80       ( ![B:$i]:
% 0.57/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.57/0.80  thf('37', plain,
% 0.57/0.80      (![X34 : $i, X35 : $i]:
% 0.57/0.80         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.57/0.80          | (v1_relat_1 @ X34)
% 0.57/0.80          | ~ (v1_relat_1 @ X35))),
% 0.57/0.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.57/0.80  thf('38', plain,
% 0.57/0.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.57/0.80        | (v1_relat_1 @ sk_D))),
% 0.57/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.57/0.80  thf(fc6_relat_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.57/0.80  thf('39', plain,
% 0.57/0.80      (![X36 : $i, X37 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X36 @ X37))),
% 0.57/0.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.57/0.80  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.57/0.80      inference('demod', [status(thm)], ['38', '39'])).
% 0.57/0.80  thf('41', plain,
% 0.57/0.80      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.57/0.80      inference('demod', [status(thm)], ['34', '35', '40'])).
% 0.57/0.80  thf('42', plain,
% 0.57/0.80      (~ (r1_tarski @ 
% 0.57/0.80          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.57/0.80          (k2_relat_1 @ sk_D))),
% 0.57/0.80      inference('demod', [status(thm)], ['30', '41'])).
% 0.57/0.80  thf('43', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_D @ 
% 0.57/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('44', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.57/0.80      inference('demod', [status(thm)], ['18', '25', '28'])).
% 0.57/0.80  thf('45', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_D @ 
% 0.57/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.57/0.80      inference('demod', [status(thm)], ['43', '44'])).
% 0.57/0.80  thf('46', plain,
% 0.57/0.80      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.57/0.80         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.57/0.80          | ((k7_relset_1 @ X48 @ X49 @ X47 @ X50) = (k9_relat_1 @ X47 @ X50)))),
% 0.57/0.80      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.57/0.80  thf('47', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.57/0.80           = (k9_relat_1 @ sk_D @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['45', '46'])).
% 0.57/0.80  thf('48', plain,
% 0.57/0.80      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.57/0.80      inference('demod', [status(thm)], ['42', '47'])).
% 0.57/0.80  thf('49', plain, (~ (v1_relat_1 @ sk_D)),
% 0.57/0.80      inference('sup-', [status(thm)], ['14', '48'])).
% 0.57/0.80  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.57/0.80      inference('demod', [status(thm)], ['38', '39'])).
% 0.57/0.80  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.57/0.80  
% 0.57/0.80  % SZS output end Refutation
% 0.57/0.80  
% 0.57/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
