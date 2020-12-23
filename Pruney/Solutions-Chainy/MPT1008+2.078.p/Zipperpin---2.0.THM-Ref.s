%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mLL2NPdWqE

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:42 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 482 expanded)
%              Number of leaves         :   35 ( 157 expanded)
%              Depth                    :   27
%              Number of atoms          : 1063 (6931 expanded)
%              Number of equality atoms :  113 ( 608 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C_2 @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( r2_hidden @ ( sk_D @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('21',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('30',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( ( sk_C_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ X0 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_D @ ( k2_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = sk_A )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['17','44'])).

thf('46',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('49',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( ( sk_C_1 @ X11 @ X12 )
        = ( k1_funct_1 @ X12 @ ( sk_D @ X11 @ X12 ) ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('53',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('58',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('61',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( ( sk_C_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( k1_funct_1 @ sk_C_2 @ sk_A )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( k1_funct_1 @ sk_C_2 @ sk_A )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mLL2NPdWqE
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:01:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 145 iterations in 0.195s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.46/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.46/0.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(t62_funct_2, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.64         ( m1_subset_1 @
% 0.46/0.64           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.64       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.64         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.46/0.64           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.64            ( m1_subset_1 @
% 0.46/0.64              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.64          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.64            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.46/0.64              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.46/0.64  thf('0', plain, ((v1_funct_2 @ sk_C_2 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d1_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.64             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.64           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.64             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_1, axiom,
% 0.46/0.64    (![C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.64       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.46/0.64          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.46/0.64          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.64        | ((k1_tarski @ sk_A)
% 0.46/0.64            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf(zf_stmt_2, axiom,
% 0.46/0.64    (![B:$i,A:$i]:
% 0.46/0.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.64       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C_2 @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_5, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.64         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.46/0.64          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.46/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.64        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0))
% 0.46/0.64        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.64  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C_2 @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.46/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)
% 0.46/0.64         = (k1_relat_1 @ sk_C_2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.46/0.64      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.46/0.64  thf(d1_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.64  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.64  thf('16', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['13', '15'])).
% 0.46/0.64  thf('17', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['13', '15'])).
% 0.46/0.64  thf(t69_enumset1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.64  thf('18', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf(d5_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.64               ( ?[D:$i]:
% 0.46/0.64                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.46/0.64                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 0.46/0.64          | (r2_hidden @ (sk_D @ X11 @ X12) @ (k1_relat_1 @ X12))
% 0.46/0.64          | ((X11) = (k2_relat_1 @ X12))
% 0.46/0.64          | ~ (v1_funct_1 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.64  thf('20', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.46/0.64      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i, X3 : $i]:
% 0.46/0.64         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)) | ((X0) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ sk_C_2)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_C_2)
% 0.46/0.64          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 0.46/0.64          | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C_2 @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc1_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( v1_relat_1 @ C ) ))).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         ((v1_relat_1 @ X18)
% 0.46/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.64  thf('27', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain, ((v1_funct_1 @ sk_C_2)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 0.46/0.64          | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i, X3 : $i]:
% 0.46/0.64         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((sk_D @ (k1_tarski @ X0) @ sk_C_2) = (sk_A))
% 0.46/0.64          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_2) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((sk_D @ (k2_tarski @ X0 @ X0) @ sk_C_2) = (sk_A))
% 0.46/0.64          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_2) = (X0))
% 0.46/0.64          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['18', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 0.46/0.64          | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 0.46/0.64          | ((sk_C_1 @ X11 @ X12) != (k1_funct_1 @ X12 @ X13))
% 0.46/0.64          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.46/0.64          | ((X11) = (k2_relat_1 @ X12))
% 0.46/0.64          | ~ (v1_funct_1 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((sk_D @ X0 @ sk_C_2) = (sk_A))
% 0.46/0.64          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ~ (v1_relat_1 @ sk_C_2)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_C_2)
% 0.46/0.64          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_C_1 @ X0 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('36', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('37', plain, ((v1_funct_1 @ sk_C_2)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((sk_D @ X0 @ sk_C_2) = (sk_A))
% 0.46/0.64          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_C_1 @ X0 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((sk_C_1 @ X0 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X1))
% 0.46/0.64          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.46/0.64          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X0) != (k1_funct_1 @ sk_C_2 @ X1))
% 0.46/0.64          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_D @ (k2_tarski @ X0 @ X0) @ sk_C_2) = (sk_A))
% 0.46/0.64          | ((sk_D @ (k1_tarski @ X0) @ sk_C_2) = (sk_A))
% 0.46/0.64          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['32', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) @ sk_C_2)
% 0.46/0.64              = (sk_A))
% 0.46/0.64          | ((sk_D @ 
% 0.46/0.64              (k2_tarski @ (k1_funct_1 @ sk_C_2 @ X1) @ 
% 0.46/0.64               (k1_funct_1 @ sk_C_2 @ X1)) @ 
% 0.46/0.64              sk_C_2) = (sk_A))
% 0.46/0.64          | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) = (k2_relat_1 @ sk_C_2)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['40'])).
% 0.46/0.64  thf('42', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) @ sk_C_2)
% 0.46/0.64              = (sk_A))
% 0.46/0.64          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) @ sk_C_2)
% 0.46/0.64              = (sk_A))
% 0.46/0.64          | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) = (k2_relat_1 @ sk_C_2)))),
% 0.46/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (((k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) @ sk_C_2)
% 0.46/0.64              = (sk_A))
% 0.46/0.64          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      ((((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2) = (sk_A))
% 0.46/0.64        | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)
% 0.46/0.64         != (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C_2 @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.46/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)
% 0.46/0.64         = (k2_relat_1 @ sk_C_2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (((k2_relat_1 @ sk_C_2) != (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2) = (sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['45', '50'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 0.46/0.64          | ((sk_C_1 @ X11 @ X12) = (k1_funct_1 @ X12 @ (sk_D @ X11 @ X12)))
% 0.46/0.64          | ((X11) = (k2_relat_1 @ X12))
% 0.46/0.64          | ~ (v1_funct_1 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X0 : $i, X3 : $i]:
% 0.46/0.64         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.46/0.64          | ((sk_C_1 @ (k1_tarski @ X0) @ X1)
% 0.46/0.64              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 0.46/0.64          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      ((((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.64          = (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.46/0.64        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.64            = (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.46/0.64        | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C_2)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C_2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['51', '54'])).
% 0.46/0.64  thf('56', plain, ((v1_funct_1 @ sk_C_2)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('57', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      ((((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.64          = (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.46/0.64        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.64            = (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.46/0.64        | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2)))),
% 0.46/0.64      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      ((((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.64            = (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (((k2_relat_1 @ sk_C_2) != (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '49'])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.64         = (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 0.46/0.64          | ((sk_C_1 @ X11 @ X12) != (k1_funct_1 @ X12 @ X13))
% 0.46/0.64          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.46/0.64          | ((X11) = (k2_relat_1 @ X12))
% 0.46/0.64          | ~ (v1_funct_1 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ 
% 0.46/0.64             (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))
% 0.46/0.64          | ~ (v1_relat_1 @ sk_C_2)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_C_2)
% 0.46/0.64          | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 0.46/0.64          | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.64              != (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf('64', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.64  thf('65', plain, ((v1_relat_1 @ sk_C_2)),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('66', plain, ((v1_funct_1 @ sk_C_2)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.46/0.64         = (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 0.46/0.64          | ((k1_funct_1 @ sk_C_2 @ sk_A) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (((k2_relat_1 @ sk_C_2) != (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '49'])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 0.46/0.64          | ((k1_funct_1 @ sk_C_2 @ sk_A) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)) | ((X0) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '22'])).
% 0.46/0.64  thf('72', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))),
% 0.46/0.64      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.64  thf('73', plain, ($false), inference('sup-', [status(thm)], ['16', '72'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
