%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gEKxOwWu9Q

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:56 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 785 expanded)
%              Number of leaves         :   49 ( 252 expanded)
%              Depth                    :   23
%              Number of atoms          : 1807 (16003 expanded)
%              Number of equality atoms :   97 ( 934 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('3',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('8',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','27','28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) @ sk_B )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('34',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('35',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['33','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('50',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) ) @ sk_B ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','52'])).

thf('54',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_E @ ( k2_funct_1 @ sk_E ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('62',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('63',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','52'])).

thf('67',plain,
    ( ( sk_B
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_E @ ( k2_funct_1 @ sk_E ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( sk_B
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_E @ ( k2_funct_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['2','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_E @ ( k2_funct_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['1','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('75',plain,
    ( ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['0','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('78',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('83',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('91',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','97'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('99',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('100',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('103',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('106',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('108',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('109',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('113',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['100','103'])).

thf('115',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('116',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['106','113','114','115','118'])).

thf('120',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C ) ),
    inference(demod,[status(thm)],['80','119'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('121',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('122',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('124',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['116','117'])).

thf('128',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('130',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('131',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','52'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('132',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('136',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_E ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['129','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('141',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['128','143'])).

thf('145',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['121','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('147',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('151',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['100','103'])).

thf('152',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['116','117'])).

thf('154',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['25','26'])).

thf('155',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['149','155'])).

thf('157',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['120','156'])).

thf('158',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('161',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['158','161'])).

thf('163',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['157','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gEKxOwWu9Q
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.22/3.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.22/3.46  % Solved by: fo/fo7.sh
% 3.22/3.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.22/3.46  % done 2021 iterations in 3.000s
% 3.22/3.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.22/3.46  % SZS output start Refutation
% 3.22/3.46  thf(sk_C_type, type, sk_C: $i).
% 3.22/3.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.22/3.46  thf(sk_A_type, type, sk_A: $i).
% 3.22/3.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.22/3.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.22/3.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.22/3.46  thf(sk_E_type, type, sk_E: $i).
% 3.22/3.46  thf(sk_B_type, type, sk_B: $i).
% 3.22/3.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.22/3.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.22/3.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.22/3.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.22/3.46  thf(sk_D_type, type, sk_D: $i).
% 3.22/3.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.22/3.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.22/3.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.22/3.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.22/3.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.22/3.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.22/3.46  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.22/3.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.22/3.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.22/3.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.22/3.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.22/3.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.22/3.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.22/3.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.22/3.46  thf(fc6_funct_1, axiom,
% 3.22/3.46    (![A:$i]:
% 3.22/3.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 3.22/3.46       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.22/3.46         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 3.22/3.46         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.22/3.46  thf('0', plain,
% 3.22/3.46      (![X9 : $i]:
% 3.22/3.46         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 3.22/3.46          | ~ (v2_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_relat_1 @ X9))),
% 3.22/3.46      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.22/3.46  thf(t160_relat_1, axiom,
% 3.22/3.46    (![A:$i]:
% 3.22/3.46     ( ( v1_relat_1 @ A ) =>
% 3.22/3.46       ( ![B:$i]:
% 3.22/3.46         ( ( v1_relat_1 @ B ) =>
% 3.22/3.46           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 3.22/3.46             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.22/3.46  thf('1', plain,
% 3.22/3.46      (![X5 : $i, X6 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X5)
% 3.22/3.46          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 3.22/3.46              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 3.22/3.46          | ~ (v1_relat_1 @ X6))),
% 3.22/3.46      inference('cnf', [status(esa)], [t160_relat_1])).
% 3.22/3.46  thf('2', plain,
% 3.22/3.46      (![X9 : $i]:
% 3.22/3.46         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 3.22/3.46          | ~ (v2_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_relat_1 @ X9))),
% 3.22/3.46      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.22/3.46  thf(t28_funct_2, conjecture,
% 3.22/3.46    (![A:$i,B:$i,C:$i,D:$i]:
% 3.22/3.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.22/3.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.22/3.46       ( ![E:$i]:
% 3.22/3.46         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.22/3.46             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.22/3.46           ( ( ( ( k2_relset_1 @
% 3.22/3.46                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.22/3.46                 ( C ) ) & 
% 3.22/3.46               ( v2_funct_1 @ E ) ) =>
% 3.22/3.46             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.22/3.46               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 3.22/3.46  thf(zf_stmt_0, negated_conjecture,
% 3.22/3.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.22/3.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.22/3.46            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.22/3.46          ( ![E:$i]:
% 3.22/3.46            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.22/3.46                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.22/3.46              ( ( ( ( k2_relset_1 @
% 3.22/3.46                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.22/3.46                    ( C ) ) & 
% 3.22/3.46                  ( v2_funct_1 @ E ) ) =>
% 3.22/3.46                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.22/3.46                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 3.22/3.46    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 3.22/3.46  thf('3', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf(d1_funct_2, axiom,
% 3.22/3.46    (![A:$i,B:$i,C:$i]:
% 3.22/3.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.22/3.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.22/3.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.22/3.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.22/3.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.22/3.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.22/3.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.22/3.46  thf(zf_stmt_1, axiom,
% 3.22/3.46    (![C:$i,B:$i,A:$i]:
% 3.22/3.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.22/3.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.22/3.46  thf('4', plain,
% 3.22/3.46      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.22/3.46         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 3.22/3.46          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 3.22/3.46          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.22/3.46  thf('5', plain,
% 3.22/3.46      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 3.22/3.46        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['3', '4'])).
% 3.22/3.46  thf(zf_stmt_2, axiom,
% 3.22/3.46    (![B:$i,A:$i]:
% 3.22/3.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.22/3.46       ( zip_tseitin_0 @ B @ A ) ))).
% 3.22/3.46  thf('6', plain,
% 3.22/3.46      (![X28 : $i, X29 : $i]:
% 3.22/3.46         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.22/3.46  thf('7', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.22/3.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.22/3.46  thf(zf_stmt_5, axiom,
% 3.22/3.46    (![A:$i,B:$i,C:$i]:
% 3.22/3.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.22/3.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.22/3.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.22/3.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.22/3.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.22/3.46  thf('8', plain,
% 3.22/3.46      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.22/3.46         (~ (zip_tseitin_0 @ X33 @ X34)
% 3.22/3.46          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 3.22/3.46          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.22/3.46  thf('9', plain,
% 3.22/3.46      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.22/3.46      inference('sup-', [status(thm)], ['7', '8'])).
% 3.22/3.46  thf('10', plain,
% 3.22/3.46      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 3.22/3.46      inference('sup-', [status(thm)], ['6', '9'])).
% 3.22/3.46  thf('11', plain, (((sk_C) != (k1_xboole_0))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('12', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 3.22/3.46      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 3.22/3.46  thf('13', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf(redefinition_k1_relset_1, axiom,
% 3.22/3.46    (![A:$i,B:$i,C:$i]:
% 3.22/3.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.22/3.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.22/3.46  thf('14', plain,
% 3.22/3.46      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.22/3.46         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 3.22/3.46          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.22/3.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.22/3.46  thf('15', plain,
% 3.22/3.46      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.22/3.46      inference('sup-', [status(thm)], ['13', '14'])).
% 3.22/3.46  thf('16', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.22/3.46      inference('demod', [status(thm)], ['5', '12', '15'])).
% 3.22/3.46  thf('17', plain,
% 3.22/3.46      (![X9 : $i]:
% 3.22/3.46         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 3.22/3.46          | ~ (v2_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_relat_1 @ X9))),
% 3.22/3.46      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.22/3.46  thf(t58_funct_1, axiom,
% 3.22/3.46    (![A:$i]:
% 3.22/3.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.22/3.46       ( ( v2_funct_1 @ A ) =>
% 3.22/3.46         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 3.22/3.46             ( k1_relat_1 @ A ) ) & 
% 3.22/3.46           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 3.22/3.46             ( k1_relat_1 @ A ) ) ) ) ))).
% 3.22/3.46  thf('18', plain,
% 3.22/3.46      (![X15 : $i]:
% 3.22/3.46         (~ (v2_funct_1 @ X15)
% 3.22/3.46          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ (k2_funct_1 @ X15)))
% 3.22/3.46              = (k1_relat_1 @ X15))
% 3.22/3.46          | ~ (v1_funct_1 @ X15)
% 3.22/3.46          | ~ (v1_relat_1 @ X15))),
% 3.22/3.46      inference('cnf', [status(esa)], [t58_funct_1])).
% 3.22/3.46  thf(t45_relat_1, axiom,
% 3.22/3.46    (![A:$i]:
% 3.22/3.46     ( ( v1_relat_1 @ A ) =>
% 3.22/3.46       ( ![B:$i]:
% 3.22/3.46         ( ( v1_relat_1 @ B ) =>
% 3.22/3.46           ( r1_tarski @
% 3.22/3.46             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.22/3.46  thf('19', plain,
% 3.22/3.46      (![X7 : $i, X8 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X7)
% 3.22/3.46          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 3.22/3.46             (k2_relat_1 @ X7))
% 3.22/3.46          | ~ (v1_relat_1 @ X8))),
% 3.22/3.46      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.22/3.46  thf('20', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.22/3.46      inference('sup+', [status(thm)], ['18', '19'])).
% 3.22/3.46  thf('21', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.22/3.46      inference('simplify', [status(thm)], ['20'])).
% 3.22/3.46  thf('22', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0))),
% 3.22/3.46      inference('sup-', [status(thm)], ['17', '21'])).
% 3.22/3.46  thf('23', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ X0))),
% 3.22/3.46      inference('simplify', [status(thm)], ['22'])).
% 3.22/3.46  thf('24', plain,
% 3.22/3.46      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_E)))
% 3.22/3.46        | ~ (v1_relat_1 @ sk_E)
% 3.22/3.46        | ~ (v1_funct_1 @ sk_E)
% 3.22/3.46        | ~ (v2_funct_1 @ sk_E))),
% 3.22/3.46      inference('sup+', [status(thm)], ['16', '23'])).
% 3.22/3.46  thf('25', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf(cc1_relset_1, axiom,
% 3.22/3.46    (![A:$i,B:$i,C:$i]:
% 3.22/3.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.22/3.46       ( v1_relat_1 @ C ) ))).
% 3.22/3.46  thf('26', plain,
% 3.22/3.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.22/3.46         ((v1_relat_1 @ X16)
% 3.22/3.46          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.22/3.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.22/3.46  thf('27', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('28', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('29', plain, ((v2_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('30', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_E)))),
% 3.22/3.46      inference('demod', [status(thm)], ['24', '27', '28', '29'])).
% 3.22/3.46  thf(d10_xboole_0, axiom,
% 3.22/3.46    (![A:$i,B:$i]:
% 3.22/3.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.22/3.46  thf('31', plain,
% 3.22/3.46      (![X0 : $i, X2 : $i]:
% 3.22/3.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.22/3.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.22/3.46  thf('32', plain,
% 3.22/3.46      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_E)) @ sk_B)
% 3.22/3.46        | ((k2_relat_1 @ (k2_funct_1 @ sk_E)) = (sk_B)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['30', '31'])).
% 3.22/3.46  thf('33', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.22/3.46      inference('demod', [status(thm)], ['5', '12', '15'])).
% 3.22/3.46  thf('34', plain,
% 3.22/3.46      (![X9 : $i]:
% 3.22/3.46         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 3.22/3.46          | ~ (v2_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_relat_1 @ X9))),
% 3.22/3.46      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.22/3.46  thf('35', plain,
% 3.22/3.46      (![X9 : $i]:
% 3.22/3.46         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 3.22/3.46          | ~ (v2_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_relat_1 @ X9))),
% 3.22/3.46      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.22/3.46  thf(t55_funct_1, axiom,
% 3.22/3.46    (![A:$i]:
% 3.22/3.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.22/3.46       ( ( v2_funct_1 @ A ) =>
% 3.22/3.46         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.22/3.46           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.22/3.46  thf('36', plain,
% 3.22/3.46      (![X14 : $i]:
% 3.22/3.46         (~ (v2_funct_1 @ X14)
% 3.22/3.46          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 3.22/3.46          | ~ (v1_funct_1 @ X14)
% 3.22/3.46          | ~ (v1_relat_1 @ X14))),
% 3.22/3.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.22/3.46  thf('37', plain,
% 3.22/3.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.22/3.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.22/3.46  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.22/3.46      inference('simplify', [status(thm)], ['37'])).
% 3.22/3.46  thf(d19_relat_1, axiom,
% 3.22/3.46    (![A:$i,B:$i]:
% 3.22/3.46     ( ( v1_relat_1 @ B ) =>
% 3.22/3.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.22/3.46  thf('39', plain,
% 3.22/3.46      (![X3 : $i, X4 : $i]:
% 3.22/3.46         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 3.22/3.46          | (v5_relat_1 @ X3 @ X4)
% 3.22/3.46          | ~ (v1_relat_1 @ X3))),
% 3.22/3.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.22/3.46  thf('40', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['38', '39'])).
% 3.22/3.46  thf('41', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.22/3.46      inference('sup+', [status(thm)], ['36', '40'])).
% 3.22/3.46  thf('42', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['35', '41'])).
% 3.22/3.46  thf('43', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ X0))),
% 3.22/3.46      inference('simplify', [status(thm)], ['42'])).
% 3.22/3.46  thf('44', plain,
% 3.22/3.46      (![X3 : $i, X4 : $i]:
% 3.22/3.46         (~ (v5_relat_1 @ X3 @ X4)
% 3.22/3.46          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 3.22/3.46          | ~ (v1_relat_1 @ X3))),
% 3.22/3.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.22/3.46  thf('45', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.22/3.46          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['43', '44'])).
% 3.22/3.46  thf('46', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ X0))),
% 3.22/3.46      inference('sup-', [status(thm)], ['34', '45'])).
% 3.22/3.46  thf('47', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ X0))),
% 3.22/3.46      inference('simplify', [status(thm)], ['46'])).
% 3.22/3.46  thf('48', plain,
% 3.22/3.46      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_E)) @ sk_B)
% 3.22/3.46        | ~ (v1_relat_1 @ sk_E)
% 3.22/3.46        | ~ (v1_funct_1 @ sk_E)
% 3.22/3.46        | ~ (v2_funct_1 @ sk_E))),
% 3.22/3.46      inference('sup+', [status(thm)], ['33', '47'])).
% 3.22/3.46  thf('49', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('50', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('51', plain, ((v2_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('52', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_E)) @ sk_B)),
% 3.22/3.46      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 3.22/3.46  thf('53', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_E)) = (sk_B))),
% 3.22/3.46      inference('demod', [status(thm)], ['32', '52'])).
% 3.22/3.46  thf('54', plain,
% 3.22/3.46      (![X15 : $i]:
% 3.22/3.46         (~ (v2_funct_1 @ X15)
% 3.22/3.46          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ (k2_funct_1 @ X15)))
% 3.22/3.46              = (k1_relat_1 @ X15))
% 3.22/3.46          | ~ (v1_funct_1 @ X15)
% 3.22/3.46          | ~ (v1_relat_1 @ X15))),
% 3.22/3.46      inference('cnf', [status(esa)], [t58_funct_1])).
% 3.22/3.46  thf('55', plain,
% 3.22/3.46      (![X7 : $i, X8 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X7)
% 3.22/3.46          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 3.22/3.46             (k2_relat_1 @ X7))
% 3.22/3.46          | ~ (v1_relat_1 @ X8))),
% 3.22/3.46      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.22/3.46  thf('56', plain,
% 3.22/3.46      (![X0 : $i, X2 : $i]:
% 3.22/3.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.22/3.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.22/3.46  thf('57', plain,
% 3.22/3.46      (![X0 : $i, X1 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X1)
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 3.22/3.46               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.22/3.46          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 3.22/3.46      inference('sup-', [status(thm)], ['55', '56'])).
% 3.22/3.46  thf('58', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 3.22/3.46              = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))
% 3.22/3.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.22/3.46          | ~ (v1_relat_1 @ X0))),
% 3.22/3.46      inference('sup-', [status(thm)], ['54', '57'])).
% 3.22/3.46  thf('59', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.22/3.46          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 3.22/3.46              = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))
% 3.22/3.46          | ~ (v2_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 3.22/3.46      inference('simplify', [status(thm)], ['58'])).
% 3.22/3.46  thf('60', plain,
% 3.22/3.46      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_E))
% 3.22/3.46        | ~ (v1_relat_1 @ sk_E)
% 3.22/3.46        | ~ (v1_funct_1 @ sk_E)
% 3.22/3.46        | ~ (v2_funct_1 @ sk_E)
% 3.22/3.46        | ((k2_relat_1 @ (k2_funct_1 @ sk_E))
% 3.22/3.46            = (k2_relat_1 @ (k5_relat_1 @ sk_E @ (k2_funct_1 @ sk_E))))
% 3.22/3.46        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['53', '59'])).
% 3.22/3.46  thf('61', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.22/3.46      inference('demod', [status(thm)], ['5', '12', '15'])).
% 3.22/3.46  thf('62', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.22/3.46      inference('simplify', [status(thm)], ['37'])).
% 3.22/3.46  thf('63', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('65', plain, ((v2_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('66', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_E)) = (sk_B))),
% 3.22/3.46      inference('demod', [status(thm)], ['32', '52'])).
% 3.22/3.46  thf('67', plain,
% 3.22/3.46      ((((sk_B) = (k2_relat_1 @ (k5_relat_1 @ sk_E @ (k2_funct_1 @ sk_E))))
% 3.22/3.46        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E)))),
% 3.22/3.46      inference('demod', [status(thm)],
% 3.22/3.46                ['60', '61', '62', '63', '64', '65', '66'])).
% 3.22/3.46  thf('68', plain,
% 3.22/3.46      ((~ (v1_relat_1 @ sk_E)
% 3.22/3.46        | ~ (v1_funct_1 @ sk_E)
% 3.22/3.46        | ~ (v2_funct_1 @ sk_E)
% 3.22/3.46        | ((sk_B) = (k2_relat_1 @ (k5_relat_1 @ sk_E @ (k2_funct_1 @ sk_E)))))),
% 3.22/3.46      inference('sup-', [status(thm)], ['2', '67'])).
% 3.22/3.46  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('71', plain, ((v2_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('72', plain,
% 3.22/3.46      (((sk_B) = (k2_relat_1 @ (k5_relat_1 @ sk_E @ (k2_funct_1 @ sk_E))))),
% 3.22/3.46      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 3.22/3.46  thf('73', plain,
% 3.22/3.46      ((((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)))
% 3.22/3.46        | ~ (v1_relat_1 @ sk_E)
% 3.22/3.46        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E)))),
% 3.22/3.46      inference('sup+', [status(thm)], ['1', '72'])).
% 3.22/3.46  thf('74', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('75', plain,
% 3.22/3.46      ((((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)))
% 3.22/3.46        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E)))),
% 3.22/3.46      inference('demod', [status(thm)], ['73', '74'])).
% 3.22/3.46  thf('76', plain,
% 3.22/3.46      ((~ (v1_relat_1 @ sk_E)
% 3.22/3.46        | ~ (v1_funct_1 @ sk_E)
% 3.22/3.46        | ~ (v2_funct_1 @ sk_E)
% 3.22/3.46        | ((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E))))),
% 3.22/3.46      inference('sup-', [status(thm)], ['0', '75'])).
% 3.22/3.46  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('78', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('79', plain, ((v2_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('80', plain,
% 3.22/3.46      (((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)))),
% 3.22/3.46      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 3.22/3.46  thf('81', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('82', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf(dt_k1_partfun1, axiom,
% 3.22/3.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.22/3.46     ( ( ( v1_funct_1 @ E ) & 
% 3.22/3.46         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.22/3.46         ( v1_funct_1 @ F ) & 
% 3.22/3.46         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.22/3.46       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.22/3.46         ( m1_subset_1 @
% 3.22/3.46           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.22/3.46           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.22/3.46  thf('83', plain,
% 3.22/3.46      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.22/3.46         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.22/3.46          | ~ (v1_funct_1 @ X36)
% 3.22/3.46          | ~ (v1_funct_1 @ X39)
% 3.22/3.46          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.22/3.46          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 3.22/3.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 3.22/3.46      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.22/3.46  thf('84', plain,
% 3.22/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.22/3.46         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 3.22/3.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.22/3.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.22/3.46          | ~ (v1_funct_1 @ X1)
% 3.22/3.46          | ~ (v1_funct_1 @ sk_D))),
% 3.22/3.46      inference('sup-', [status(thm)], ['82', '83'])).
% 3.22/3.46  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('86', plain,
% 3.22/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.22/3.46         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 3.22/3.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.22/3.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.22/3.46          | ~ (v1_funct_1 @ X1))),
% 3.22/3.46      inference('demod', [status(thm)], ['84', '85'])).
% 3.22/3.46  thf('87', plain,
% 3.22/3.46      ((~ (v1_funct_1 @ sk_E)
% 3.22/3.46        | (m1_subset_1 @ 
% 3.22/3.46           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 3.22/3.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 3.22/3.46      inference('sup-', [status(thm)], ['81', '86'])).
% 3.22/3.46  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('89', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('90', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf(redefinition_k1_partfun1, axiom,
% 3.22/3.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.22/3.46     ( ( ( v1_funct_1 @ E ) & 
% 3.22/3.46         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.22/3.46         ( v1_funct_1 @ F ) & 
% 3.22/3.46         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.22/3.46       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.22/3.46  thf('91', plain,
% 3.22/3.46      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 3.22/3.46         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.22/3.46          | ~ (v1_funct_1 @ X42)
% 3.22/3.46          | ~ (v1_funct_1 @ X45)
% 3.22/3.46          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 3.22/3.46          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 3.22/3.46              = (k5_relat_1 @ X42 @ X45)))),
% 3.22/3.46      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.22/3.46  thf('92', plain,
% 3.22/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.22/3.46         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.22/3.46            = (k5_relat_1 @ sk_D @ X0))
% 3.22/3.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.22/3.46          | ~ (v1_funct_1 @ X0)
% 3.22/3.46          | ~ (v1_funct_1 @ sk_D))),
% 3.22/3.46      inference('sup-', [status(thm)], ['90', '91'])).
% 3.22/3.46  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('94', plain,
% 3.22/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.22/3.46         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.22/3.46            = (k5_relat_1 @ sk_D @ X0))
% 3.22/3.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.22/3.46          | ~ (v1_funct_1 @ X0))),
% 3.22/3.46      inference('demod', [status(thm)], ['92', '93'])).
% 3.22/3.46  thf('95', plain,
% 3.22/3.46      ((~ (v1_funct_1 @ sk_E)
% 3.22/3.46        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.22/3.46            = (k5_relat_1 @ sk_D @ sk_E)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['89', '94'])).
% 3.22/3.46  thf('96', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('97', plain,
% 3.22/3.46      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.22/3.46         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.22/3.46      inference('demod', [status(thm)], ['95', '96'])).
% 3.22/3.46  thf('98', plain,
% 3.22/3.46      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 3.22/3.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.22/3.46      inference('demod', [status(thm)], ['87', '88', '97'])).
% 3.22/3.46  thf(redefinition_k2_relset_1, axiom,
% 3.22/3.46    (![A:$i,B:$i,C:$i]:
% 3.22/3.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.22/3.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.22/3.46  thf('99', plain,
% 3.22/3.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.22/3.46         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 3.22/3.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.22/3.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.22/3.46  thf('100', plain,
% 3.22/3.46      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 3.22/3.46         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['98', '99'])).
% 3.22/3.46  thf('101', plain,
% 3.22/3.46      (((k2_relset_1 @ sk_A @ sk_C @ 
% 3.22/3.46         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('102', plain,
% 3.22/3.46      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.22/3.46         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.22/3.46      inference('demod', [status(thm)], ['95', '96'])).
% 3.22/3.46  thf('103', plain,
% 3.22/3.46      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.22/3.46      inference('demod', [status(thm)], ['101', '102'])).
% 3.22/3.46  thf('104', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.22/3.46      inference('sup+', [status(thm)], ['100', '103'])).
% 3.22/3.46  thf('105', plain,
% 3.22/3.46      (![X0 : $i, X1 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X1)
% 3.22/3.46          | ~ (v1_relat_1 @ X0)
% 3.22/3.46          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 3.22/3.46               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.22/3.46          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 3.22/3.46      inference('sup-', [status(thm)], ['55', '56'])).
% 3.22/3.46  thf('106', plain,
% 3.22/3.46      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 3.22/3.46        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 3.22/3.46        | ~ (v1_relat_1 @ sk_E)
% 3.22/3.46        | ~ (v1_relat_1 @ sk_D))),
% 3.22/3.46      inference('sup-', [status(thm)], ['104', '105'])).
% 3.22/3.46  thf('107', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf(cc2_relset_1, axiom,
% 3.22/3.46    (![A:$i,B:$i,C:$i]:
% 3.22/3.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.22/3.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.22/3.46  thf('108', plain,
% 3.22/3.46      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.22/3.46         ((v5_relat_1 @ X19 @ X21)
% 3.22/3.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.22/3.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.22/3.46  thf('109', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 3.22/3.46      inference('sup-', [status(thm)], ['107', '108'])).
% 3.22/3.46  thf('110', plain,
% 3.22/3.46      (![X3 : $i, X4 : $i]:
% 3.22/3.46         (~ (v5_relat_1 @ X3 @ X4)
% 3.22/3.46          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 3.22/3.46          | ~ (v1_relat_1 @ X3))),
% 3.22/3.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.22/3.46  thf('111', plain,
% 3.22/3.46      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 3.22/3.46      inference('sup-', [status(thm)], ['109', '110'])).
% 3.22/3.46  thf('112', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('113', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 3.22/3.46      inference('demod', [status(thm)], ['111', '112'])).
% 3.22/3.46  thf('114', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.22/3.46      inference('sup+', [status(thm)], ['100', '103'])).
% 3.22/3.46  thf('115', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('116', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('117', plain,
% 3.22/3.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.22/3.46         ((v1_relat_1 @ X16)
% 3.22/3.46          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.22/3.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.22/3.46  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 3.22/3.46      inference('sup-', [status(thm)], ['116', '117'])).
% 3.22/3.46  thf('119', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 3.22/3.46      inference('demod', [status(thm)], ['106', '113', '114', '115', '118'])).
% 3.22/3.46  thf('120', plain, (((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C))),
% 3.22/3.46      inference('demod', [status(thm)], ['80', '119'])).
% 3.22/3.46  thf(t154_funct_1, axiom,
% 3.22/3.46    (![A:$i,B:$i]:
% 3.22/3.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.22/3.46       ( ( v2_funct_1 @ B ) =>
% 3.22/3.46         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 3.22/3.46  thf('121', plain,
% 3.22/3.46      (![X12 : $i, X13 : $i]:
% 3.22/3.46         (~ (v2_funct_1 @ X12)
% 3.22/3.46          | ((k9_relat_1 @ X12 @ X13)
% 3.22/3.46              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 3.22/3.46          | ~ (v1_funct_1 @ X12)
% 3.22/3.46          | ~ (v1_relat_1 @ X12))),
% 3.22/3.46      inference('cnf', [status(esa)], [t154_funct_1])).
% 3.22/3.46  thf('122', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('123', plain,
% 3.22/3.46      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.22/3.46         ((v5_relat_1 @ X19 @ X21)
% 3.22/3.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.22/3.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.22/3.46  thf('124', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 3.22/3.46      inference('sup-', [status(thm)], ['122', '123'])).
% 3.22/3.46  thf('125', plain,
% 3.22/3.46      (![X3 : $i, X4 : $i]:
% 3.22/3.46         (~ (v5_relat_1 @ X3 @ X4)
% 3.22/3.46          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 3.22/3.46          | ~ (v1_relat_1 @ X3))),
% 3.22/3.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.22/3.46  thf('126', plain,
% 3.22/3.46      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 3.22/3.46      inference('sup-', [status(thm)], ['124', '125'])).
% 3.22/3.46  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 3.22/3.46      inference('sup-', [status(thm)], ['116', '117'])).
% 3.22/3.46  thf('128', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 3.22/3.46      inference('demod', [status(thm)], ['126', '127'])).
% 3.22/3.46  thf('129', plain,
% 3.22/3.46      (![X9 : $i]:
% 3.22/3.46         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 3.22/3.46          | ~ (v2_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_relat_1 @ X9))),
% 3.22/3.46      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.22/3.46  thf('130', plain,
% 3.22/3.46      (![X9 : $i]:
% 3.22/3.46         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 3.22/3.46          | ~ (v2_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_funct_1 @ X9)
% 3.22/3.46          | ~ (v1_relat_1 @ X9))),
% 3.22/3.46      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.22/3.46  thf('131', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_E)) = (sk_B))),
% 3.22/3.46      inference('demod', [status(thm)], ['32', '52'])).
% 3.22/3.46  thf(t147_funct_1, axiom,
% 3.22/3.46    (![A:$i,B:$i]:
% 3.22/3.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.22/3.46       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 3.22/3.46         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.22/3.46  thf('132', plain,
% 3.22/3.46      (![X10 : $i, X11 : $i]:
% 3.22/3.46         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 3.22/3.46          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 3.22/3.46          | ~ (v1_funct_1 @ X11)
% 3.22/3.46          | ~ (v1_relat_1 @ X11))),
% 3.22/3.46      inference('cnf', [status(esa)], [t147_funct_1])).
% 3.22/3.46  thf('133', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (r1_tarski @ X0 @ sk_B)
% 3.22/3.46          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_E))
% 3.22/3.46          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 3.22/3.46          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 3.22/3.46              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['131', '132'])).
% 3.22/3.46  thf('134', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ sk_E)
% 3.22/3.46          | ~ (v1_funct_1 @ sk_E)
% 3.22/3.46          | ~ (v2_funct_1 @ sk_E)
% 3.22/3.46          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 3.22/3.46              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0))
% 3.22/3.46          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 3.22/3.46          | ~ (r1_tarski @ X0 @ sk_B))),
% 3.22/3.46      inference('sup-', [status(thm)], ['130', '133'])).
% 3.22/3.46  thf('135', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('136', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('137', plain, ((v2_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('138', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 3.22/3.46            (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0))
% 3.22/3.46          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_E))
% 3.22/3.46          | ~ (r1_tarski @ X0 @ sk_B))),
% 3.22/3.46      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 3.22/3.46  thf('139', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ sk_E)
% 3.22/3.46          | ~ (v1_funct_1 @ sk_E)
% 3.22/3.46          | ~ (v2_funct_1 @ sk_E)
% 3.22/3.46          | ~ (r1_tarski @ X0 @ sk_B)
% 3.22/3.46          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 3.22/3.46              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0)))),
% 3.22/3.46      inference('sup-', [status(thm)], ['129', '138'])).
% 3.22/3.46  thf('140', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('141', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('142', plain, ((v2_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('143', plain,
% 3.22/3.46      (![X0 : $i]:
% 3.22/3.46         (~ (r1_tarski @ X0 @ sk_B)
% 3.22/3.46          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 3.22/3.46              (k10_relat_1 @ (k2_funct_1 @ sk_E) @ X0)) = (X0)))),
% 3.22/3.46      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 3.22/3.46  thf('144', plain,
% 3.22/3.46      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 3.22/3.46         (k10_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_D)))
% 3.22/3.46         = (k2_relat_1 @ sk_D))),
% 3.22/3.46      inference('sup-', [status(thm)], ['128', '143'])).
% 3.22/3.46  thf('145', plain,
% 3.22/3.46      ((((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 3.22/3.46          (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))) = (k2_relat_1 @ sk_D))
% 3.22/3.46        | ~ (v1_relat_1 @ sk_E)
% 3.22/3.46        | ~ (v1_funct_1 @ sk_E)
% 3.22/3.46        | ~ (v2_funct_1 @ sk_E))),
% 3.22/3.46      inference('sup+', [status(thm)], ['121', '144'])).
% 3.22/3.46  thf('146', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('147', plain, ((v1_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('148', plain, ((v2_funct_1 @ sk_E)),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('149', plain,
% 3.22/3.46      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 3.22/3.46         (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))) = (k2_relat_1 @ sk_D))),
% 3.22/3.46      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 3.22/3.46  thf('150', plain,
% 3.22/3.46      (![X5 : $i, X6 : $i]:
% 3.22/3.46         (~ (v1_relat_1 @ X5)
% 3.22/3.46          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 3.22/3.46              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 3.22/3.46          | ~ (v1_relat_1 @ X6))),
% 3.22/3.46      inference('cnf', [status(esa)], [t160_relat_1])).
% 3.22/3.46  thf('151', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.22/3.46      inference('sup+', [status(thm)], ['100', '103'])).
% 3.22/3.46  thf('152', plain,
% 3.22/3.46      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 3.22/3.46        | ~ (v1_relat_1 @ sk_D)
% 3.22/3.46        | ~ (v1_relat_1 @ sk_E))),
% 3.22/3.46      inference('sup+', [status(thm)], ['150', '151'])).
% 3.22/3.46  thf('153', plain, ((v1_relat_1 @ sk_D)),
% 3.22/3.46      inference('sup-', [status(thm)], ['116', '117'])).
% 3.22/3.46  thf('154', plain, ((v1_relat_1 @ sk_E)),
% 3.22/3.46      inference('sup-', [status(thm)], ['25', '26'])).
% 3.22/3.46  thf('155', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 3.22/3.46      inference('demod', [status(thm)], ['152', '153', '154'])).
% 3.22/3.46  thf('156', plain,
% 3.22/3.46      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) = (k2_relat_1 @ sk_D))),
% 3.22/3.46      inference('demod', [status(thm)], ['149', '155'])).
% 3.22/3.46  thf('157', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 3.22/3.46      inference('sup+', [status(thm)], ['120', '156'])).
% 3.22/3.46  thf('158', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('159', plain,
% 3.22/3.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.22/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.46  thf('160', plain,
% 3.22/3.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.22/3.46         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 3.22/3.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.22/3.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.22/3.46  thf('161', plain,
% 3.22/3.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.22/3.46      inference('sup-', [status(thm)], ['159', '160'])).
% 3.22/3.46  thf('162', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 3.22/3.46      inference('demod', [status(thm)], ['158', '161'])).
% 3.22/3.46  thf('163', plain, ($false),
% 3.22/3.46      inference('simplify_reflect-', [status(thm)], ['157', '162'])).
% 3.22/3.46  
% 3.22/3.46  % SZS output end Refutation
% 3.22/3.46  
% 3.22/3.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
