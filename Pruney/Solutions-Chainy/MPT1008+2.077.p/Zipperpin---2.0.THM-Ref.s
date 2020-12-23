%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2YlbvvlYxy

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:42 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 482 expanded)
%              Number of leaves         :   35 ( 157 expanded)
%              Depth                    :   27
%              Number of atoms          : 1063 (6931 expanded)
%              Number of equality atoms :  113 ( 608 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    v1_funct_2 @ sk_C_3 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_3 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_3 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_3 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
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
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X12 @ X13 ) @ X12 )
      | ( r2_hidden @ ( sk_D @ X12 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ( X12
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
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
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_3 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_3 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('30',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 )
        = sk_A )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup+',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_3 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X12 @ X13 ) @ X12 )
      | ( ( sk_C_2 @ X12 @ X13 )
       != ( k1_funct_1 @ X13 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ( X12
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_C_3 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ X0 @ sk_C_3 )
       != ( k1_funct_1 @ sk_C_3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_C_3 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ X0 @ sk_C_3 )
       != ( k1_funct_1 @ sk_C_3 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_C_3 )
       != ( k1_funct_1 @ sk_C_3 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_D @ X0 @ sk_C_3 )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_funct_1 @ sk_C_3 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ X1 ) ) @ sk_C_3 )
        = sk_A )
      | ( ( sk_D @ ( k2_tarski @ ( k1_funct_1 @ sk_C_3 @ X1 ) @ ( k1_funct_1 @ sk_C_3 @ X1 ) ) @ sk_C_3 )
        = sk_A )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ X1 ) )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ X1 ) ) @ sk_C_3 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ X1 ) ) @ sk_C_3 )
        = sk_A )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ X1 ) )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ X1 ) )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ X1 ) ) @ sk_C_3 )
        = sk_A )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
      = sk_A )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['17','44'])).

thf('46',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_3 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('49',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X12 @ X13 ) @ X12 )
      | ( ( sk_C_2 @ X12 @ X13 )
        = ( k1_funct_1 @ X13 @ ( sk_D @ X12 @ X13 ) ) )
      | ( X12
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
      = ( k1_funct_1 @ sk_C_3 @ sk_A ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
      = ( k1_funct_1 @ sk_C_3 @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_3 ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('58',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
      = ( k1_funct_1 @ sk_C_3 @ sk_A ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
      = ( k1_funct_1 @ sk_C_3 @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
      = ( k1_funct_1 @ sk_C_3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('61',plain,
    ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
    = ( k1_funct_1 @ sk_C_3 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X12 @ X13 ) @ X12 )
      | ( ( sk_C_2 @ X12 @ X13 )
       != ( k1_funct_1 @ X13 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ( X12
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
       != ( k1_funct_1 @ sk_C_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) @ sk_C_3 )
    = ( k1_funct_1 @ sk_C_3 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( ( k1_funct_1 @ sk_C_3 @ sk_A )
       != ( k1_funct_1 @ sk_C_3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( ( k1_funct_1 @ sk_C_3 @ sk_A )
       != ( k1_funct_1 @ sk_C_3 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2YlbvvlYxy
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:44:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.16/4.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.16/4.36  % Solved by: fo/fo7.sh
% 4.16/4.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.16/4.36  % done 1672 iterations in 3.922s
% 4.16/4.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.16/4.36  % SZS output start Refutation
% 4.16/4.36  thf(sk_C_3_type, type, sk_C_3: $i).
% 4.16/4.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.16/4.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.16/4.36  thf(sk_B_type, type, sk_B: $i).
% 4.16/4.36  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 4.16/4.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.16/4.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.16/4.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.16/4.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.16/4.36  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.16/4.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.16/4.36  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.16/4.36  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.16/4.36  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 4.16/4.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.16/4.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.16/4.36  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.16/4.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.16/4.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.16/4.36  thf(sk_A_type, type, sk_A: $i).
% 4.16/4.36  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.16/4.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.16/4.36  thf(t62_funct_2, conjecture,
% 4.16/4.36    (![A:$i,B:$i,C:$i]:
% 4.16/4.36     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 4.16/4.36         ( m1_subset_1 @
% 4.16/4.36           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 4.16/4.36       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 4.16/4.36         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 4.16/4.36           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 4.16/4.36  thf(zf_stmt_0, negated_conjecture,
% 4.16/4.36    (~( ![A:$i,B:$i,C:$i]:
% 4.16/4.36        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 4.16/4.36            ( m1_subset_1 @
% 4.16/4.36              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 4.16/4.36          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 4.16/4.36            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 4.16/4.36              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 4.16/4.36    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 4.16/4.36  thf('0', plain, ((v1_funct_2 @ sk_C_3 @ (k1_tarski @ sk_A) @ sk_B)),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf(d1_funct_2, axiom,
% 4.16/4.36    (![A:$i,B:$i,C:$i]:
% 4.16/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.36       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.16/4.36           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.16/4.36             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.16/4.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.16/4.36           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.16/4.36             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.16/4.36  thf(zf_stmt_1, axiom,
% 4.16/4.36    (![C:$i,B:$i,A:$i]:
% 4.16/4.36     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.16/4.36       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.16/4.36  thf('1', plain,
% 4.16/4.36      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.16/4.36         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 4.16/4.36          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 4.16/4.36          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.16/4.36  thf('2', plain,
% 4.16/4.36      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B @ (k1_tarski @ sk_A))
% 4.16/4.36        | ((k1_tarski @ sk_A)
% 4.16/4.36            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_3)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['0', '1'])).
% 4.16/4.36  thf(zf_stmt_2, axiom,
% 4.16/4.36    (![B:$i,A:$i]:
% 4.16/4.36     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.16/4.36       ( zip_tseitin_0 @ B @ A ) ))).
% 4.16/4.36  thf('3', plain,
% 4.16/4.36      (![X28 : $i, X29 : $i]:
% 4.16/4.36         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.16/4.36  thf('4', plain,
% 4.16/4.36      ((m1_subset_1 @ sk_C_3 @ 
% 4.16/4.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.16/4.36  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.16/4.36  thf(zf_stmt_5, axiom,
% 4.16/4.36    (![A:$i,B:$i,C:$i]:
% 4.16/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.36       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.16/4.36         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.16/4.36           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.16/4.36             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.16/4.36  thf('5', plain,
% 4.16/4.36      (![X33 : $i, X34 : $i, X35 : $i]:
% 4.16/4.36         (~ (zip_tseitin_0 @ X33 @ X34)
% 4.16/4.36          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 4.16/4.36          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.16/4.36  thf('6', plain,
% 4.16/4.36      (((zip_tseitin_1 @ sk_C_3 @ sk_B @ (k1_tarski @ sk_A))
% 4.16/4.36        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['4', '5'])).
% 4.16/4.36  thf('7', plain,
% 4.16/4.36      ((((sk_B) = (k1_xboole_0))
% 4.16/4.36        | (zip_tseitin_1 @ sk_C_3 @ sk_B @ (k1_tarski @ sk_A)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['3', '6'])).
% 4.16/4.36  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf('9', plain, ((zip_tseitin_1 @ sk_C_3 @ sk_B @ (k1_tarski @ sk_A))),
% 4.16/4.36      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 4.16/4.36  thf('10', plain,
% 4.16/4.36      ((m1_subset_1 @ sk_C_3 @ 
% 4.16/4.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf(redefinition_k1_relset_1, axiom,
% 4.16/4.36    (![A:$i,B:$i,C:$i]:
% 4.16/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.36       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.16/4.36  thf('11', plain,
% 4.16/4.36      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.16/4.36         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 4.16/4.36          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 4.16/4.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.16/4.36  thf('12', plain,
% 4.16/4.36      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_3)
% 4.16/4.36         = (k1_relat_1 @ sk_C_3))),
% 4.16/4.36      inference('sup-', [status(thm)], ['10', '11'])).
% 4.16/4.36  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 4.16/4.36      inference('demod', [status(thm)], ['2', '9', '12'])).
% 4.16/4.36  thf(d1_tarski, axiom,
% 4.16/4.36    (![A:$i,B:$i]:
% 4.16/4.36     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 4.16/4.36       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 4.16/4.36  thf('14', plain,
% 4.16/4.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.36         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 4.16/4.36      inference('cnf', [status(esa)], [d1_tarski])).
% 4.16/4.36  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.16/4.36      inference('simplify', [status(thm)], ['14'])).
% 4.16/4.36  thf('16', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 4.16/4.36      inference('sup+', [status(thm)], ['13', '15'])).
% 4.16/4.36  thf('17', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 4.16/4.36      inference('sup+', [status(thm)], ['13', '15'])).
% 4.16/4.36  thf(t69_enumset1, axiom,
% 4.16/4.36    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.16/4.36  thf('18', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 4.16/4.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.16/4.36  thf(d5_funct_1, axiom,
% 4.16/4.36    (![A:$i]:
% 4.16/4.36     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.16/4.36       ( ![B:$i]:
% 4.16/4.36         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 4.16/4.36           ( ![C:$i]:
% 4.16/4.36             ( ( r2_hidden @ C @ B ) <=>
% 4.16/4.36               ( ?[D:$i]:
% 4.16/4.36                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 4.16/4.36                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 4.16/4.36  thf('19', plain,
% 4.16/4.36      (![X12 : $i, X13 : $i]:
% 4.16/4.36         ((r2_hidden @ (sk_C_2 @ X12 @ X13) @ X12)
% 4.16/4.36          | (r2_hidden @ (sk_D @ X12 @ X13) @ (k1_relat_1 @ X13))
% 4.16/4.36          | ((X12) = (k2_relat_1 @ X13))
% 4.16/4.36          | ~ (v1_funct_1 @ X13)
% 4.16/4.36          | ~ (v1_relat_1 @ X13))),
% 4.16/4.36      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.16/4.36  thf('20', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 4.16/4.36      inference('demod', [status(thm)], ['2', '9', '12'])).
% 4.16/4.36  thf('21', plain,
% 4.16/4.36      (![X0 : $i, X2 : $i, X3 : $i]:
% 4.16/4.36         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 4.16/4.36      inference('cnf', [status(esa)], [d1_tarski])).
% 4.16/4.36  thf('22', plain,
% 4.16/4.36      (![X0 : $i, X3 : $i]:
% 4.16/4.36         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 4.16/4.36      inference('simplify', [status(thm)], ['21'])).
% 4.16/4.36  thf('23', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3)) | ((X0) = (sk_A)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['20', '22'])).
% 4.16/4.36  thf('24', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (~ (v1_relat_1 @ sk_C_3)
% 4.16/4.36          | ~ (v1_funct_1 @ sk_C_3)
% 4.16/4.36          | ((X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ X0)
% 4.16/4.36          | ((sk_D @ X0 @ sk_C_3) = (sk_A)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['19', '23'])).
% 4.16/4.36  thf('25', plain,
% 4.16/4.36      ((m1_subset_1 @ sk_C_3 @ 
% 4.16/4.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf(cc1_relset_1, axiom,
% 4.16/4.36    (![A:$i,B:$i,C:$i]:
% 4.16/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.36       ( v1_relat_1 @ C ) ))).
% 4.16/4.36  thf('26', plain,
% 4.16/4.36      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.16/4.36         ((v1_relat_1 @ X19)
% 4.16/4.36          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.16/4.36      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.16/4.36  thf('27', plain, ((v1_relat_1 @ sk_C_3)),
% 4.16/4.36      inference('sup-', [status(thm)], ['25', '26'])).
% 4.16/4.36  thf('28', plain, ((v1_funct_1 @ sk_C_3)),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf('29', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (((X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ X0)
% 4.16/4.36          | ((sk_D @ X0 @ sk_C_3) = (sk_A)))),
% 4.16/4.36      inference('demod', [status(thm)], ['24', '27', '28'])).
% 4.16/4.36  thf('30', plain,
% 4.16/4.36      (![X0 : $i, X3 : $i]:
% 4.16/4.36         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 4.16/4.36      inference('simplify', [status(thm)], ['21'])).
% 4.16/4.36  thf('31', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (((sk_D @ (k1_tarski @ X0) @ sk_C_3) = (sk_A))
% 4.16/4.36          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['29', '30'])).
% 4.16/4.36  thf('32', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (((sk_D @ (k2_tarski @ X0 @ X0) @ sk_C_3) = (sk_A))
% 4.16/4.36          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0))
% 4.16/4.36          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3)))),
% 4.16/4.36      inference('sup+', [status(thm)], ['18', '31'])).
% 4.16/4.36  thf('33', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (((X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ X0)
% 4.16/4.36          | ((sk_D @ X0 @ sk_C_3) = (sk_A)))),
% 4.16/4.36      inference('demod', [status(thm)], ['24', '27', '28'])).
% 4.16/4.36  thf('34', plain,
% 4.16/4.36      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.16/4.36         (~ (r2_hidden @ (sk_C_2 @ X12 @ X13) @ X12)
% 4.16/4.36          | ((sk_C_2 @ X12 @ X13) != (k1_funct_1 @ X13 @ X14))
% 4.16/4.36          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 4.16/4.36          | ((X12) = (k2_relat_1 @ X13))
% 4.16/4.36          | ~ (v1_funct_1 @ X13)
% 4.16/4.36          | ~ (v1_relat_1 @ X13))),
% 4.16/4.36      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.16/4.36  thf('35', plain,
% 4.16/4.36      (![X0 : $i, X1 : $i]:
% 4.16/4.36         (((sk_D @ X0 @ sk_C_3) = (sk_A))
% 4.16/4.36          | ((X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ~ (v1_relat_1 @ sk_C_3)
% 4.16/4.36          | ~ (v1_funct_1 @ sk_C_3)
% 4.16/4.36          | ((X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_C_2 @ X0 @ sk_C_3) != (k1_funct_1 @ sk_C_3 @ X1)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['33', '34'])).
% 4.16/4.36  thf('36', plain, ((v1_relat_1 @ sk_C_3)),
% 4.16/4.36      inference('sup-', [status(thm)], ['25', '26'])).
% 4.16/4.36  thf('37', plain, ((v1_funct_1 @ sk_C_3)),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf('38', plain,
% 4.16/4.36      (![X0 : $i, X1 : $i]:
% 4.16/4.36         (((sk_D @ X0 @ sk_C_3) = (sk_A))
% 4.16/4.36          | ((X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ((X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_C_2 @ X0 @ sk_C_3) != (k1_funct_1 @ sk_C_3 @ X1)))),
% 4.16/4.36      inference('demod', [status(thm)], ['35', '36', '37'])).
% 4.16/4.36  thf('39', plain,
% 4.16/4.36      (![X0 : $i, X1 : $i]:
% 4.16/4.36         (((sk_C_2 @ X0 @ sk_C_3) != (k1_funct_1 @ sk_C_3 @ X1))
% 4.16/4.36          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_3))
% 4.16/4.36          | ((X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_D @ X0 @ sk_C_3) = (sk_A)))),
% 4.16/4.36      inference('simplify', [status(thm)], ['38'])).
% 4.16/4.36  thf('40', plain,
% 4.16/4.36      (![X0 : $i, X1 : $i]:
% 4.16/4.36         (((X0) != (k1_funct_1 @ sk_C_3 @ X1))
% 4.16/4.36          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_D @ (k2_tarski @ X0 @ X0) @ sk_C_3) = (sk_A))
% 4.16/4.36          | ((sk_D @ (k1_tarski @ X0) @ sk_C_3) = (sk_A))
% 4.16/4.36          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_3)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['32', '39'])).
% 4.16/4.36  thf('41', plain,
% 4.16/4.36      (![X1 : $i]:
% 4.16/4.36         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ X1)) @ sk_C_3)
% 4.16/4.36              = (sk_A))
% 4.16/4.36          | ((sk_D @ 
% 4.16/4.36              (k2_tarski @ (k1_funct_1 @ sk_C_3 @ X1) @ 
% 4.16/4.36               (k1_funct_1 @ sk_C_3 @ X1)) @ 
% 4.16/4.36              sk_C_3) = (sk_A))
% 4.16/4.36          | ((k1_tarski @ (k1_funct_1 @ sk_C_3 @ X1)) = (k2_relat_1 @ sk_C_3)))),
% 4.16/4.36      inference('simplify', [status(thm)], ['40'])).
% 4.16/4.36  thf('42', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 4.16/4.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.16/4.36  thf('43', plain,
% 4.16/4.36      (![X1 : $i]:
% 4.16/4.36         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ X1)) @ sk_C_3)
% 4.16/4.36              = (sk_A))
% 4.16/4.36          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ X1)) @ sk_C_3)
% 4.16/4.36              = (sk_A))
% 4.16/4.36          | ((k1_tarski @ (k1_funct_1 @ sk_C_3 @ X1)) = (k2_relat_1 @ sk_C_3)))),
% 4.16/4.36      inference('demod', [status(thm)], ['41', '42'])).
% 4.16/4.36  thf('44', plain,
% 4.16/4.36      (![X1 : $i]:
% 4.16/4.36         (((k1_tarski @ (k1_funct_1 @ sk_C_3 @ X1)) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ X1)) @ sk_C_3)
% 4.16/4.36              = (sk_A))
% 4.16/4.36          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_3)))),
% 4.16/4.36      inference('simplify', [status(thm)], ['43'])).
% 4.16/4.36  thf('45', plain,
% 4.16/4.36      ((((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3) = (sk_A))
% 4.16/4.36        | ((k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) = (k2_relat_1 @ sk_C_3)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['17', '44'])).
% 4.16/4.36  thf('46', plain,
% 4.16/4.36      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_3)
% 4.16/4.36         != (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf('47', plain,
% 4.16/4.36      ((m1_subset_1 @ sk_C_3 @ 
% 4.16/4.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf(redefinition_k2_relset_1, axiom,
% 4.16/4.36    (![A:$i,B:$i,C:$i]:
% 4.16/4.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.36       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.16/4.36  thf('48', plain,
% 4.16/4.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.16/4.36         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 4.16/4.36          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.16/4.36      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.16/4.36  thf('49', plain,
% 4.16/4.36      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_3)
% 4.16/4.36         = (k2_relat_1 @ sk_C_3))),
% 4.16/4.36      inference('sup-', [status(thm)], ['47', '48'])).
% 4.16/4.36  thf('50', plain,
% 4.16/4.36      (((k2_relat_1 @ sk_C_3) != (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)))),
% 4.16/4.36      inference('demod', [status(thm)], ['46', '49'])).
% 4.16/4.36  thf('51', plain,
% 4.16/4.36      (((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3) = (sk_A))),
% 4.16/4.36      inference('simplify_reflect-', [status(thm)], ['45', '50'])).
% 4.16/4.36  thf('52', plain,
% 4.16/4.36      (![X12 : $i, X13 : $i]:
% 4.16/4.36         ((r2_hidden @ (sk_C_2 @ X12 @ X13) @ X12)
% 4.16/4.36          | ((sk_C_2 @ X12 @ X13) = (k1_funct_1 @ X13 @ (sk_D @ X12 @ X13)))
% 4.16/4.36          | ((X12) = (k2_relat_1 @ X13))
% 4.16/4.36          | ~ (v1_funct_1 @ X13)
% 4.16/4.36          | ~ (v1_relat_1 @ X13))),
% 4.16/4.36      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.16/4.36  thf('53', plain,
% 4.16/4.36      (![X0 : $i, X3 : $i]:
% 4.16/4.36         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 4.16/4.36      inference('simplify', [status(thm)], ['21'])).
% 4.16/4.36  thf('54', plain,
% 4.16/4.36      (![X0 : $i, X1 : $i]:
% 4.16/4.36         (~ (v1_relat_1 @ X1)
% 4.16/4.36          | ~ (v1_funct_1 @ X1)
% 4.16/4.36          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 4.16/4.36          | ((sk_C_2 @ (k1_tarski @ X0) @ X1)
% 4.16/4.36              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 4.16/4.36          | ((sk_C_2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['52', '53'])).
% 4.16/4.36  thf('55', plain,
% 4.16/4.36      ((((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3)
% 4.16/4.36          = (k1_funct_1 @ sk_C_3 @ sk_A))
% 4.16/4.36        | ((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3)
% 4.16/4.36            = (k1_funct_1 @ sk_C_3 @ sk_A))
% 4.16/4.36        | ((k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36        | ~ (v1_funct_1 @ sk_C_3)
% 4.16/4.36        | ~ (v1_relat_1 @ sk_C_3))),
% 4.16/4.36      inference('sup+', [status(thm)], ['51', '54'])).
% 4.16/4.36  thf('56', plain, ((v1_funct_1 @ sk_C_3)),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf('57', plain, ((v1_relat_1 @ sk_C_3)),
% 4.16/4.36      inference('sup-', [status(thm)], ['25', '26'])).
% 4.16/4.36  thf('58', plain,
% 4.16/4.36      ((((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3)
% 4.16/4.36          = (k1_funct_1 @ sk_C_3 @ sk_A))
% 4.16/4.36        | ((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3)
% 4.16/4.36            = (k1_funct_1 @ sk_C_3 @ sk_A))
% 4.16/4.36        | ((k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) = (k2_relat_1 @ sk_C_3)))),
% 4.16/4.36      inference('demod', [status(thm)], ['55', '56', '57'])).
% 4.16/4.36  thf('59', plain,
% 4.16/4.36      ((((k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36        | ((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3)
% 4.16/4.36            = (k1_funct_1 @ sk_C_3 @ sk_A)))),
% 4.16/4.36      inference('simplify', [status(thm)], ['58'])).
% 4.16/4.36  thf('60', plain,
% 4.16/4.36      (((k2_relat_1 @ sk_C_3) != (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)))),
% 4.16/4.36      inference('demod', [status(thm)], ['46', '49'])).
% 4.16/4.36  thf('61', plain,
% 4.16/4.36      (((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3)
% 4.16/4.36         = (k1_funct_1 @ sk_C_3 @ sk_A))),
% 4.16/4.36      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 4.16/4.36  thf('62', plain,
% 4.16/4.36      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.16/4.36         (~ (r2_hidden @ (sk_C_2 @ X12 @ X13) @ X12)
% 4.16/4.36          | ((sk_C_2 @ X12 @ X13) != (k1_funct_1 @ X13 @ X14))
% 4.16/4.36          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 4.16/4.36          | ((X12) = (k2_relat_1 @ X13))
% 4.16/4.36          | ~ (v1_funct_1 @ X13)
% 4.16/4.36          | ~ (v1_relat_1 @ X13))),
% 4.16/4.36      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.16/4.36  thf('63', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (~ (r2_hidden @ (k1_funct_1 @ sk_C_3 @ sk_A) @ 
% 4.16/4.36             (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)))
% 4.16/4.36          | ~ (v1_relat_1 @ sk_C_3)
% 4.16/4.36          | ~ (v1_funct_1 @ sk_C_3)
% 4.16/4.36          | ((k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3))
% 4.16/4.36          | ((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3)
% 4.16/4.36              != (k1_funct_1 @ sk_C_3 @ X0)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['61', '62'])).
% 4.16/4.36  thf('64', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.16/4.36      inference('simplify', [status(thm)], ['14'])).
% 4.16/4.36  thf('65', plain, ((v1_relat_1 @ sk_C_3)),
% 4.16/4.36      inference('sup-', [status(thm)], ['25', '26'])).
% 4.16/4.36  thf('66', plain, ((v1_funct_1 @ sk_C_3)),
% 4.16/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.36  thf('67', plain,
% 4.16/4.36      (((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) @ sk_C_3)
% 4.16/4.36         = (k1_funct_1 @ sk_C_3 @ sk_A))),
% 4.16/4.36      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 4.16/4.36  thf('68', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (((k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)) = (k2_relat_1 @ sk_C_3))
% 4.16/4.36          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3))
% 4.16/4.36          | ((k1_funct_1 @ sk_C_3 @ sk_A) != (k1_funct_1 @ sk_C_3 @ X0)))),
% 4.16/4.36      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 4.16/4.36  thf('69', plain,
% 4.16/4.36      (((k2_relat_1 @ sk_C_3) != (k1_tarski @ (k1_funct_1 @ sk_C_3 @ sk_A)))),
% 4.16/4.36      inference('demod', [status(thm)], ['46', '49'])).
% 4.16/4.36  thf('70', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3))
% 4.16/4.36          | ((k1_funct_1 @ sk_C_3 @ sk_A) != (k1_funct_1 @ sk_C_3 @ X0)))),
% 4.16/4.36      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 4.16/4.36  thf('71', plain,
% 4.16/4.36      (![X0 : $i]:
% 4.16/4.36         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3)) | ((X0) = (sk_A)))),
% 4.16/4.36      inference('sup-', [status(thm)], ['20', '22'])).
% 4.16/4.36  thf('72', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3))),
% 4.16/4.36      inference('clc', [status(thm)], ['70', '71'])).
% 4.16/4.36  thf('73', plain, ($false), inference('sup-', [status(thm)], ['16', '72'])).
% 4.16/4.36  
% 4.16/4.36  % SZS output end Refutation
% 4.16/4.36  
% 4.16/4.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
