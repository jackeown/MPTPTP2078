%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xvksjMnHDb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:11 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 366 expanded)
%              Number of leaves         :   49 ( 131 expanded)
%              Depth                    :   15
%              Number of atoms          : 1817 (8648 expanded)
%              Number of equality atoms :  142 ( 649 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( X65 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X66 )
      | ~ ( v1_funct_2 @ X66 @ X67 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X65 ) ) )
      | ( ( k5_relat_1 @ X66 @ ( k2_funct_1 @ X66 ) )
        = ( k6_partfun1 @ X67 ) )
      | ~ ( v2_funct_1 @ X66 )
      | ( ( k2_relset_1 @ X67 @ X65 @ X66 )
       != X65 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('18',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('22',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','26','29'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('31',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('32',plain,(
    ! [X61: $i] :
      ( ( k6_partfun1 @ X61 )
      = ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( v2_funct_1 @ X62 )
      | ( ( k2_relset_1 @ X64 @ X63 @ X62 )
       != X63 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X62 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X63 ) ) )
      | ~ ( v1_funct_2 @ X62 @ X64 @ X63 )
      | ~ ( v1_funct_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('55',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('59',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['16','30','33','35','40','53','54','55','56','57','58'])).

thf('60',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('63',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( ( k1_partfun1 @ X56 @ X57 @ X59 @ X60 @ X55 @ X58 )
        = ( k5_relat_1 @ X55 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('73',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('78',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k4_relset_1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('82',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( X42 = X45 )
      | ~ ( r2_relset_1 @ X43 @ X44 @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','83'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('85',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('86',plain,(
    ! [X61: $i] :
      ( ( k6_partfun1 @ X61 )
      = ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','87'])).

thf(l72_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( ( k2_relat_1 @ B )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('89',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X15 )
       != X14 )
      | ( ( k5_relat_1 @ X15 @ X13 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ( ( k5_relat_1 @ X13 @ X16 )
       != ( k6_relat_1 @ X14 ) )
      | ( X16 = X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('90',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16 = X15 )
      | ( ( k5_relat_1 @ X13 @ X16 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k5_relat_1 @ X15 @ X13 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X61: $i] :
      ( ( k6_partfun1 @ X61 )
      = ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X61: $i] :
      ( ( k6_partfun1 @ X61 )
      = ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16 = X15 )
      | ( ( k5_relat_1 @ X13 @ X16 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k5_relat_1 @ X15 @ X13 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_A )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('99',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('103',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('109',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['99','106','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_A )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_partfun1 @ sk_B ) )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96','110','111','116'])).

thf('118',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','117'])).

thf('119',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( v2_funct_1 @ X62 )
      | ( ( k2_relset_1 @ X64 @ X63 @ X62 )
       != X63 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X63 ) ) )
      | ~ ( v1_funct_2 @ X62 @ X64 @ X63 )
      | ~ ( v1_funct_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( X65 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X66 )
      | ~ ( v1_funct_2 @ X66 @ X67 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X65 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X66 ) @ X66 )
        = ( k6_partfun1 @ X65 ) )
      | ~ ( v2_funct_1 @ X66 )
      | ( ( k2_relset_1 @ X67 @ X65 @ X66 )
       != X65 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('131',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119','128','139'])).

thf('141',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['141','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xvksjMnHDb
% 0.13/0.36  % Computer   : n004.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:41:09 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 2.55/2.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.55/2.72  % Solved by: fo/fo7.sh
% 2.55/2.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.55/2.72  % done 1029 iterations in 2.231s
% 2.55/2.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.55/2.72  % SZS output start Refutation
% 2.55/2.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.55/2.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.55/2.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.55/2.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.55/2.72  thf(sk_D_type, type, sk_D: $i).
% 2.55/2.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.55/2.72  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.55/2.72  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.55/2.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.55/2.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.55/2.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.55/2.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.55/2.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.55/2.72  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.55/2.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.55/2.72  thf(sk_A_type, type, sk_A: $i).
% 2.55/2.72  thf(sk_C_type, type, sk_C: $i).
% 2.55/2.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.55/2.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.55/2.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.55/2.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.55/2.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.55/2.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.55/2.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.55/2.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.55/2.72  thf(sk_B_type, type, sk_B: $i).
% 2.55/2.72  thf(t36_funct_2, conjecture,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.55/2.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.72       ( ![D:$i]:
% 2.55/2.72         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.55/2.72             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.55/2.72           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.55/2.72               ( r2_relset_1 @
% 2.55/2.72                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.55/2.72                 ( k6_partfun1 @ A ) ) & 
% 2.55/2.72               ( v2_funct_1 @ C ) ) =>
% 2.55/2.72             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.55/2.72               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.55/2.72  thf(zf_stmt_0, negated_conjecture,
% 2.55/2.72    (~( ![A:$i,B:$i,C:$i]:
% 2.55/2.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.55/2.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.72          ( ![D:$i]:
% 2.55/2.72            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.55/2.72                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.55/2.72              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.55/2.72                  ( r2_relset_1 @
% 2.55/2.72                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.55/2.72                    ( k6_partfun1 @ A ) ) & 
% 2.55/2.72                  ( v2_funct_1 @ C ) ) =>
% 2.55/2.72                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.55/2.72                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.55/2.72    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.55/2.72  thf('0', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(t35_funct_2, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.55/2.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.72       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.55/2.72         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.55/2.72           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.55/2.72             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.55/2.72  thf('1', plain,
% 2.55/2.72      (![X65 : $i, X66 : $i, X67 : $i]:
% 2.55/2.72         (((X65) = (k1_xboole_0))
% 2.55/2.72          | ~ (v1_funct_1 @ X66)
% 2.55/2.72          | ~ (v1_funct_2 @ X66 @ X67 @ X65)
% 2.55/2.72          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X65)))
% 2.55/2.72          | ((k5_relat_1 @ X66 @ (k2_funct_1 @ X66)) = (k6_partfun1 @ X67))
% 2.55/2.72          | ~ (v2_funct_1 @ X66)
% 2.55/2.72          | ((k2_relset_1 @ X67 @ X65 @ X66) != (X65)))),
% 2.55/2.72      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.55/2.72  thf('2', plain,
% 2.55/2.72      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.55/2.72        | ~ (v2_funct_1 @ sk_C)
% 2.55/2.72        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 2.55/2.72        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.55/2.72        | ~ (v1_funct_1 @ sk_C)
% 2.55/2.72        | ((sk_B) = (k1_xboole_0)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['0', '1'])).
% 2.55/2.72  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('4', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('7', plain,
% 2.55/2.72      ((((sk_B) != (sk_B))
% 2.55/2.72        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 2.55/2.72        | ((sk_B) = (k1_xboole_0)))),
% 2.55/2.72      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 2.55/2.72  thf('8', plain,
% 2.55/2.72      ((((sk_B) = (k1_xboole_0))
% 2.55/2.72        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 2.55/2.72      inference('simplify', [status(thm)], ['7'])).
% 2.55/2.72  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('10', plain,
% 2.55/2.72      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 2.55/2.72      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 2.55/2.72  thf(t55_funct_1, axiom,
% 2.55/2.72    (![A:$i]:
% 2.55/2.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.55/2.72       ( ( v2_funct_1 @ A ) =>
% 2.55/2.72         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.55/2.72           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.55/2.72  thf('11', plain,
% 2.55/2.72      (![X19 : $i]:
% 2.55/2.72         (~ (v2_funct_1 @ X19)
% 2.55/2.72          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 2.55/2.72          | ~ (v1_funct_1 @ X19)
% 2.55/2.72          | ~ (v1_relat_1 @ X19))),
% 2.55/2.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.55/2.72  thf(t45_relat_1, axiom,
% 2.55/2.72    (![A:$i]:
% 2.55/2.72     ( ( v1_relat_1 @ A ) =>
% 2.55/2.72       ( ![B:$i]:
% 2.55/2.72         ( ( v1_relat_1 @ B ) =>
% 2.55/2.72           ( r1_tarski @
% 2.55/2.72             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.55/2.72  thf('12', plain,
% 2.55/2.72      (![X9 : $i, X10 : $i]:
% 2.55/2.72         (~ (v1_relat_1 @ X9)
% 2.55/2.72          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 2.55/2.72             (k2_relat_1 @ X9))
% 2.55/2.72          | ~ (v1_relat_1 @ X10))),
% 2.55/2.72      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.55/2.72  thf(d10_xboole_0, axiom,
% 2.55/2.72    (![A:$i,B:$i]:
% 2.55/2.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.55/2.72  thf('13', plain,
% 2.55/2.72      (![X0 : $i, X2 : $i]:
% 2.55/2.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.55/2.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.55/2.72  thf('14', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         (~ (v1_relat_1 @ X1)
% 2.55/2.72          | ~ (v1_relat_1 @ X0)
% 2.55/2.72          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.55/2.72               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.55/2.72          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.55/2.72      inference('sup-', [status(thm)], ['12', '13'])).
% 2.55/2.72  thf('15', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]:
% 2.55/2.72         (~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.55/2.72             (k2_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0))))
% 2.55/2.72          | ~ (v1_relat_1 @ X0)
% 2.55/2.72          | ~ (v1_funct_1 @ X0)
% 2.55/2.72          | ~ (v2_funct_1 @ X0)
% 2.55/2.72          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.55/2.72              = (k2_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0))))
% 2.55/2.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.55/2.72          | ~ (v1_relat_1 @ X1))),
% 2.55/2.72      inference('sup-', [status(thm)], ['11', '14'])).
% 2.55/2.72  thf('16', plain,
% 2.55/2.72      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.72           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 2.55/2.72        | ~ (v1_relat_1 @ sk_C)
% 2.55/2.72        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.55/2.72        | ((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 2.55/2.72            = (k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))
% 2.55/2.72        | ~ (v2_funct_1 @ sk_C)
% 2.55/2.72        | ~ (v1_funct_1 @ sk_C)
% 2.55/2.72        | ~ (v1_relat_1 @ sk_C))),
% 2.55/2.72      inference('sup-', [status(thm)], ['10', '15'])).
% 2.55/2.72  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(d1_funct_2, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.55/2.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.55/2.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.55/2.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.55/2.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.55/2.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.55/2.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.55/2.72  thf(zf_stmt_1, axiom,
% 2.55/2.72    (![C:$i,B:$i,A:$i]:
% 2.55/2.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.55/2.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.55/2.72  thf('18', plain,
% 2.55/2.72      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.55/2.72         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 2.55/2.72          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 2.55/2.72          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.55/2.72  thf('19', plain,
% 2.55/2.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.55/2.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['17', '18'])).
% 2.55/2.72  thf(zf_stmt_2, axiom,
% 2.55/2.72    (![B:$i,A:$i]:
% 2.55/2.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.55/2.72       ( zip_tseitin_0 @ B @ A ) ))).
% 2.55/2.72  thf('20', plain,
% 2.55/2.72      (![X47 : $i, X48 : $i]:
% 2.55/2.72         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.55/2.72  thf('21', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.55/2.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.55/2.72  thf(zf_stmt_5, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.55/2.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.55/2.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.55/2.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.55/2.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.55/2.72  thf('22', plain,
% 2.55/2.72      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.55/2.72         (~ (zip_tseitin_0 @ X52 @ X53)
% 2.55/2.72          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 2.55/2.72          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.55/2.72  thf('23', plain,
% 2.55/2.72      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.55/2.72      inference('sup-', [status(thm)], ['21', '22'])).
% 2.55/2.72  thf('24', plain,
% 2.55/2.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.55/2.72      inference('sup-', [status(thm)], ['20', '23'])).
% 2.55/2.72  thf('25', plain, (((sk_B) != (k1_xboole_0))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('26', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 2.55/2.72      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 2.55/2.72  thf('27', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(redefinition_k1_relset_1, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.55/2.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.55/2.72  thf('28', plain,
% 2.55/2.72      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.55/2.72         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 2.55/2.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.55/2.72  thf('29', plain,
% 2.55/2.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.55/2.72      inference('sup-', [status(thm)], ['27', '28'])).
% 2.55/2.72  thf('30', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.55/2.72      inference('demod', [status(thm)], ['19', '26', '29'])).
% 2.55/2.72  thf(t71_relat_1, axiom,
% 2.55/2.72    (![A:$i]:
% 2.55/2.72     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.55/2.72       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.55/2.72  thf('31', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 2.55/2.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.55/2.72  thf(redefinition_k6_partfun1, axiom,
% 2.55/2.72    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.55/2.72  thf('32', plain, (![X61 : $i]: ((k6_partfun1 @ X61) = (k6_relat_1 @ X61))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.55/2.72  thf('33', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 2.55/2.72      inference('demod', [status(thm)], ['31', '32'])).
% 2.55/2.72  thf('34', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.55/2.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.55/2.72  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.55/2.72      inference('simplify', [status(thm)], ['34'])).
% 2.55/2.72  thf('36', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(cc2_relat_1, axiom,
% 2.55/2.72    (![A:$i]:
% 2.55/2.72     ( ( v1_relat_1 @ A ) =>
% 2.55/2.72       ( ![B:$i]:
% 2.55/2.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.55/2.72  thf('37', plain,
% 2.55/2.72      (![X3 : $i, X4 : $i]:
% 2.55/2.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.55/2.72          | (v1_relat_1 @ X3)
% 2.55/2.72          | ~ (v1_relat_1 @ X4))),
% 2.55/2.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.55/2.72  thf('38', plain,
% 2.55/2.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.55/2.72      inference('sup-', [status(thm)], ['36', '37'])).
% 2.55/2.72  thf(fc6_relat_1, axiom,
% 2.55/2.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.55/2.72  thf('39', plain,
% 2.55/2.72      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.55/2.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.55/2.72  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.72      inference('demod', [status(thm)], ['38', '39'])).
% 2.55/2.72  thf('41', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(t31_funct_2, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i]:
% 2.55/2.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.55/2.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.72       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.55/2.72         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.55/2.72           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.55/2.72           ( m1_subset_1 @
% 2.55/2.72             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.55/2.72  thf('42', plain,
% 2.55/2.72      (![X62 : $i, X63 : $i, X64 : $i]:
% 2.55/2.72         (~ (v2_funct_1 @ X62)
% 2.55/2.72          | ((k2_relset_1 @ X64 @ X63 @ X62) != (X63))
% 2.55/2.72          | (m1_subset_1 @ (k2_funct_1 @ X62) @ 
% 2.55/2.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64)))
% 2.55/2.72          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X63)))
% 2.55/2.72          | ~ (v1_funct_2 @ X62 @ X64 @ X63)
% 2.55/2.72          | ~ (v1_funct_1 @ X62))),
% 2.55/2.72      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.55/2.72  thf('43', plain,
% 2.55/2.72      ((~ (v1_funct_1 @ sk_C)
% 2.55/2.72        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.55/2.72        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.55/2.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.55/2.72        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.55/2.72        | ~ (v2_funct_1 @ sk_C))),
% 2.55/2.72      inference('sup-', [status(thm)], ['41', '42'])).
% 2.55/2.72  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('45', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('46', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('48', plain,
% 2.55/2.72      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.55/2.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.55/2.72        | ((sk_B) != (sk_B)))),
% 2.55/2.72      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 2.55/2.72  thf('49', plain,
% 2.55/2.72      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.55/2.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.55/2.72      inference('simplify', [status(thm)], ['48'])).
% 2.55/2.72  thf('50', plain,
% 2.55/2.72      (![X3 : $i, X4 : $i]:
% 2.55/2.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.55/2.72          | (v1_relat_1 @ X3)
% 2.55/2.72          | ~ (v1_relat_1 @ X4))),
% 2.55/2.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.55/2.72  thf('51', plain,
% 2.55/2.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 2.55/2.72        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['49', '50'])).
% 2.55/2.72  thf('52', plain,
% 2.55/2.72      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.55/2.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.55/2.72  thf('53', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.55/2.72      inference('demod', [status(thm)], ['51', '52'])).
% 2.55/2.72  thf('54', plain,
% 2.55/2.72      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 2.55/2.72      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 2.55/2.72  thf('55', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 2.55/2.72      inference('demod', [status(thm)], ['31', '32'])).
% 2.55/2.72  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.72      inference('demod', [status(thm)], ['38', '39'])).
% 2.55/2.72  thf('59', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 2.55/2.72      inference('demod', [status(thm)],
% 2.55/2.72                ['16', '30', '33', '35', '40', '53', '54', '55', '56', '57', 
% 2.55/2.72                 '58'])).
% 2.55/2.72  thf('60', plain,
% 2.55/2.72      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.55/2.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.55/2.72        (k6_partfun1 @ sk_A))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('61', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('62', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(redefinition_k1_partfun1, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.55/2.72     ( ( ( v1_funct_1 @ E ) & 
% 2.55/2.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.55/2.72         ( v1_funct_1 @ F ) & 
% 2.55/2.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.55/2.72       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.55/2.72  thf('63', plain,
% 2.55/2.72      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 2.55/2.72         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 2.55/2.72          | ~ (v1_funct_1 @ X55)
% 2.55/2.72          | ~ (v1_funct_1 @ X58)
% 2.55/2.72          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 2.55/2.72          | ((k1_partfun1 @ X56 @ X57 @ X59 @ X60 @ X55 @ X58)
% 2.55/2.72              = (k5_relat_1 @ X55 @ X58)))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.55/2.72  thf('64', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.72         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.55/2.72            = (k5_relat_1 @ sk_C @ X0))
% 2.55/2.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.55/2.72          | ~ (v1_funct_1 @ X0)
% 2.55/2.72          | ~ (v1_funct_1 @ sk_C))),
% 2.55/2.72      inference('sup-', [status(thm)], ['62', '63'])).
% 2.55/2.72  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('66', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.72         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.55/2.72            = (k5_relat_1 @ sk_C @ X0))
% 2.55/2.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.55/2.72          | ~ (v1_funct_1 @ X0))),
% 2.55/2.72      inference('demod', [status(thm)], ['64', '65'])).
% 2.55/2.72  thf('67', plain,
% 2.55/2.72      ((~ (v1_funct_1 @ sk_D)
% 2.55/2.72        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.55/2.72            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['61', '66'])).
% 2.55/2.72  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('69', plain,
% 2.55/2.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.55/2.72         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.55/2.72      inference('demod', [status(thm)], ['67', '68'])).
% 2.55/2.72  thf('70', plain,
% 2.55/2.72      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.55/2.72        (k6_partfun1 @ sk_A))),
% 2.55/2.72      inference('demod', [status(thm)], ['60', '69'])).
% 2.55/2.72  thf('71', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('72', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(dt_k4_relset_1, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.55/2.72     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.55/2.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.55/2.72       ( m1_subset_1 @
% 2.55/2.72         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.55/2.72         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.55/2.72  thf('73', plain,
% 2.55/2.72      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.55/2.72         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.55/2.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.55/2.72          | (m1_subset_1 @ (k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 2.55/2.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 2.55/2.72      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.55/2.72  thf('74', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.72         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.55/2.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.55/2.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.55/2.72      inference('sup-', [status(thm)], ['72', '73'])).
% 2.55/2.72  thf('75', plain,
% 2.55/2.72      ((m1_subset_1 @ 
% 2.55/2.72        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.55/2.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['71', '74'])).
% 2.55/2.72  thf('76', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('77', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf(redefinition_k4_relset_1, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.55/2.72     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.55/2.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.55/2.72       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.55/2.72  thf('78', plain,
% 2.55/2.72      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.55/2.72         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.55/2.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.55/2.72          | ((k4_relset_1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 2.55/2.72              = (k5_relat_1 @ X36 @ X39)))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.55/2.72  thf('79', plain,
% 2.55/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.72         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.55/2.72            = (k5_relat_1 @ sk_C @ X0))
% 2.55/2.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.55/2.72      inference('sup-', [status(thm)], ['77', '78'])).
% 2.55/2.72  thf('80', plain,
% 2.55/2.72      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.55/2.72         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.55/2.72      inference('sup-', [status(thm)], ['76', '79'])).
% 2.55/2.72  thf('81', plain,
% 2.55/2.72      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.55/2.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.55/2.72      inference('demod', [status(thm)], ['75', '80'])).
% 2.55/2.72  thf(redefinition_r2_relset_1, axiom,
% 2.55/2.72    (![A:$i,B:$i,C:$i,D:$i]:
% 2.55/2.72     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.55/2.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.72       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.55/2.72  thf('82', plain,
% 2.55/2.72      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 2.55/2.72         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 2.55/2.72          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 2.55/2.72          | ((X42) = (X45))
% 2.55/2.72          | ~ (r2_relset_1 @ X43 @ X44 @ X42 @ X45))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.55/2.72  thf('83', plain,
% 2.55/2.72      (![X0 : $i]:
% 2.55/2.72         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.55/2.72          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.55/2.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.55/2.72      inference('sup-', [status(thm)], ['81', '82'])).
% 2.55/2.72  thf('84', plain,
% 2.55/2.72      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.55/2.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.55/2.72        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['70', '83'])).
% 2.55/2.72  thf(t29_relset_1, axiom,
% 2.55/2.72    (![A:$i]:
% 2.55/2.72     ( m1_subset_1 @
% 2.55/2.72       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.55/2.72  thf('85', plain,
% 2.55/2.72      (![X46 : $i]:
% 2.55/2.72         (m1_subset_1 @ (k6_relat_1 @ X46) @ 
% 2.55/2.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 2.55/2.72      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.55/2.72  thf('86', plain, (![X61 : $i]: ((k6_partfun1 @ X61) = (k6_relat_1 @ X61))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.55/2.72  thf('87', plain,
% 2.55/2.72      (![X46 : $i]:
% 2.55/2.72         (m1_subset_1 @ (k6_partfun1 @ X46) @ 
% 2.55/2.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 2.55/2.72      inference('demod', [status(thm)], ['85', '86'])).
% 2.55/2.72  thf('88', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.55/2.72      inference('demod', [status(thm)], ['84', '87'])).
% 2.55/2.72  thf(l72_funct_1, axiom,
% 2.55/2.72    (![A:$i,B:$i]:
% 2.55/2.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.55/2.72       ( ![C:$i]:
% 2.55/2.72         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.55/2.72           ( ![D:$i]:
% 2.55/2.72             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 2.55/2.72               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 2.55/2.72                   ( ( k5_relat_1 @ B @ C ) =
% 2.55/2.72                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 2.55/2.72                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 2.55/2.72                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 2.55/2.72  thf('89', plain,
% 2.55/2.72      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.55/2.72         (~ (v1_relat_1 @ X13)
% 2.55/2.72          | ~ (v1_funct_1 @ X13)
% 2.55/2.72          | ((k2_relat_1 @ X15) != (X14))
% 2.55/2.72          | ((k5_relat_1 @ X15 @ X13) != (k6_relat_1 @ (k1_relat_1 @ X16)))
% 2.55/2.72          | ((k5_relat_1 @ X13 @ X16) != (k6_relat_1 @ X14))
% 2.55/2.72          | ((X16) = (X15))
% 2.55/2.72          | ~ (v1_funct_1 @ X16)
% 2.55/2.72          | ~ (v1_relat_1 @ X16)
% 2.55/2.72          | ~ (v1_funct_1 @ X15)
% 2.55/2.72          | ~ (v1_relat_1 @ X15))),
% 2.55/2.72      inference('cnf', [status(esa)], [l72_funct_1])).
% 2.55/2.72  thf('90', plain,
% 2.55/2.72      (![X13 : $i, X15 : $i, X16 : $i]:
% 2.55/2.72         (~ (v1_relat_1 @ X15)
% 2.55/2.72          | ~ (v1_funct_1 @ X15)
% 2.55/2.72          | ~ (v1_relat_1 @ X16)
% 2.55/2.72          | ~ (v1_funct_1 @ X16)
% 2.55/2.72          | ((X16) = (X15))
% 2.55/2.72          | ((k5_relat_1 @ X13 @ X16) != (k6_relat_1 @ (k2_relat_1 @ X15)))
% 2.55/2.72          | ((k5_relat_1 @ X15 @ X13) != (k6_relat_1 @ (k1_relat_1 @ X16)))
% 2.55/2.72          | ~ (v1_funct_1 @ X13)
% 2.55/2.72          | ~ (v1_relat_1 @ X13))),
% 2.55/2.72      inference('simplify', [status(thm)], ['89'])).
% 2.55/2.72  thf('91', plain, (![X61 : $i]: ((k6_partfun1 @ X61) = (k6_relat_1 @ X61))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.55/2.72  thf('92', plain, (![X61 : $i]: ((k6_partfun1 @ X61) = (k6_relat_1 @ X61))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.55/2.72  thf('93', plain,
% 2.55/2.72      (![X13 : $i, X15 : $i, X16 : $i]:
% 2.55/2.72         (~ (v1_relat_1 @ X15)
% 2.55/2.72          | ~ (v1_funct_1 @ X15)
% 2.55/2.72          | ~ (v1_relat_1 @ X16)
% 2.55/2.72          | ~ (v1_funct_1 @ X16)
% 2.55/2.72          | ((X16) = (X15))
% 2.55/2.72          | ((k5_relat_1 @ X13 @ X16) != (k6_partfun1 @ (k2_relat_1 @ X15)))
% 2.55/2.72          | ((k5_relat_1 @ X15 @ X13) != (k6_partfun1 @ (k1_relat_1 @ X16)))
% 2.55/2.72          | ~ (v1_funct_1 @ X13)
% 2.55/2.72          | ~ (v1_relat_1 @ X13))),
% 2.55/2.72      inference('demod', [status(thm)], ['90', '91', '92'])).
% 2.55/2.72  thf('94', plain,
% 2.55/2.72      (![X0 : $i]:
% 2.55/2.72         (((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 2.55/2.72          | ~ (v1_relat_1 @ sk_C)
% 2.55/2.72          | ~ (v1_funct_1 @ sk_C)
% 2.55/2.72          | ((k5_relat_1 @ X0 @ sk_C) != (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 2.55/2.72          | ((sk_D) = (X0))
% 2.55/2.72          | ~ (v1_funct_1 @ sk_D)
% 2.55/2.72          | ~ (v1_relat_1 @ sk_D)
% 2.55/2.72          | ~ (v1_funct_1 @ X0)
% 2.55/2.72          | ~ (v1_relat_1 @ X0))),
% 2.55/2.72      inference('sup-', [status(thm)], ['88', '93'])).
% 2.55/2.72  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.72      inference('demod', [status(thm)], ['38', '39'])).
% 2.55/2.72  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('97', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('98', plain,
% 2.55/2.72      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.55/2.72         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 2.55/2.72          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 2.55/2.72          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.55/2.72  thf('99', plain,
% 2.55/2.72      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 2.55/2.72        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['97', '98'])).
% 2.55/2.72  thf('100', plain,
% 2.55/2.72      (![X47 : $i, X48 : $i]:
% 2.55/2.72         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.55/2.72  thf('101', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('102', plain,
% 2.55/2.72      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.55/2.72         (~ (zip_tseitin_0 @ X52 @ X53)
% 2.55/2.72          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 2.55/2.72          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.55/2.72  thf('103', plain,
% 2.55/2.72      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 2.55/2.72      inference('sup-', [status(thm)], ['101', '102'])).
% 2.55/2.72  thf('104', plain,
% 2.55/2.72      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 2.55/2.72      inference('sup-', [status(thm)], ['100', '103'])).
% 2.55/2.72  thf('105', plain, (((sk_A) != (k1_xboole_0))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('106', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 2.55/2.72      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 2.55/2.72  thf('107', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('108', plain,
% 2.55/2.72      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.55/2.72         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 2.55/2.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 2.55/2.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.55/2.72  thf('109', plain,
% 2.55/2.72      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.55/2.72      inference('sup-', [status(thm)], ['107', '108'])).
% 2.55/2.72  thf('110', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.55/2.72      inference('demod', [status(thm)], ['99', '106', '109'])).
% 2.55/2.72  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('112', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('113', plain,
% 2.55/2.72      (![X3 : $i, X4 : $i]:
% 2.55/2.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.55/2.72          | (v1_relat_1 @ X3)
% 2.55/2.72          | ~ (v1_relat_1 @ X4))),
% 2.55/2.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.55/2.72  thf('114', plain,
% 2.55/2.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.55/2.72      inference('sup-', [status(thm)], ['112', '113'])).
% 2.55/2.72  thf('115', plain,
% 2.55/2.72      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.55/2.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.55/2.72  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 2.55/2.72      inference('demod', [status(thm)], ['114', '115'])).
% 2.55/2.72  thf('117', plain,
% 2.55/2.72      (![X0 : $i]:
% 2.55/2.72         (((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 2.55/2.72          | ((k5_relat_1 @ X0 @ sk_C) != (k6_partfun1 @ sk_B))
% 2.55/2.72          | ((sk_D) = (X0))
% 2.55/2.72          | ~ (v1_funct_1 @ X0)
% 2.55/2.72          | ~ (v1_relat_1 @ X0))),
% 2.55/2.72      inference('demod', [status(thm)], ['94', '95', '96', '110', '111', '116'])).
% 2.55/2.72  thf('118', plain,
% 2.55/2.72      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 2.55/2.72        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.55/2.72        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.55/2.72        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.55/2.72        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) != (k6_partfun1 @ sk_B)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['59', '117'])).
% 2.55/2.72  thf('119', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.55/2.72      inference('demod', [status(thm)], ['51', '52'])).
% 2.55/2.72  thf('120', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('121', plain,
% 2.55/2.72      (![X62 : $i, X63 : $i, X64 : $i]:
% 2.55/2.72         (~ (v2_funct_1 @ X62)
% 2.55/2.72          | ((k2_relset_1 @ X64 @ X63 @ X62) != (X63))
% 2.55/2.72          | (v1_funct_1 @ (k2_funct_1 @ X62))
% 2.55/2.72          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X63)))
% 2.55/2.72          | ~ (v1_funct_2 @ X62 @ X64 @ X63)
% 2.55/2.72          | ~ (v1_funct_1 @ X62))),
% 2.55/2.72      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.55/2.72  thf('122', plain,
% 2.55/2.72      ((~ (v1_funct_1 @ sk_C)
% 2.55/2.72        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.55/2.72        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.55/2.72        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.55/2.72        | ~ (v2_funct_1 @ sk_C))),
% 2.55/2.72      inference('sup-', [status(thm)], ['120', '121'])).
% 2.55/2.72  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('124', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('125', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('127', plain,
% 2.55/2.72      (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 2.55/2.72      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 2.55/2.72  thf('128', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.55/2.72      inference('simplify', [status(thm)], ['127'])).
% 2.55/2.72  thf('129', plain,
% 2.55/2.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('130', plain,
% 2.55/2.72      (![X65 : $i, X66 : $i, X67 : $i]:
% 2.55/2.72         (((X65) = (k1_xboole_0))
% 2.55/2.72          | ~ (v1_funct_1 @ X66)
% 2.55/2.72          | ~ (v1_funct_2 @ X66 @ X67 @ X65)
% 2.55/2.72          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X65)))
% 2.55/2.72          | ((k5_relat_1 @ (k2_funct_1 @ X66) @ X66) = (k6_partfun1 @ X65))
% 2.55/2.72          | ~ (v2_funct_1 @ X66)
% 2.55/2.72          | ((k2_relset_1 @ X67 @ X65 @ X66) != (X65)))),
% 2.55/2.72      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.55/2.72  thf('131', plain,
% 2.55/2.72      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.55/2.72        | ~ (v2_funct_1 @ sk_C)
% 2.55/2.72        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.55/2.72        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.55/2.72        | ~ (v1_funct_1 @ sk_C)
% 2.55/2.72        | ((sk_B) = (k1_xboole_0)))),
% 2.55/2.72      inference('sup-', [status(thm)], ['129', '130'])).
% 2.55/2.72  thf('132', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('134', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('136', plain,
% 2.55/2.72      ((((sk_B) != (sk_B))
% 2.55/2.72        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.55/2.72        | ((sk_B) = (k1_xboole_0)))),
% 2.55/2.72      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 2.55/2.72  thf('137', plain,
% 2.55/2.72      ((((sk_B) = (k1_xboole_0))
% 2.55/2.72        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 2.55/2.72      inference('simplify', [status(thm)], ['136'])).
% 2.55/2.72  thf('138', plain, (((sk_B) != (k1_xboole_0))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('139', plain,
% 2.55/2.72      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.55/2.72      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 2.55/2.72  thf('140', plain,
% 2.55/2.72      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 2.55/2.72        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.55/2.72        | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B)))),
% 2.55/2.72      inference('demod', [status(thm)], ['118', '119', '128', '139'])).
% 2.55/2.72  thf('141', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 2.55/2.72      inference('simplify', [status(thm)], ['140'])).
% 2.55/2.72  thf('142', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.55/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.72  thf('143', plain, ($false),
% 2.55/2.72      inference('simplify_reflect-', [status(thm)], ['141', '142'])).
% 2.55/2.72  
% 2.55/2.72  % SZS output end Refutation
% 2.55/2.72  
% 2.55/2.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
