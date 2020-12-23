%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tYSDv5vPMK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:57 EST 2020

% Result     : Theorem 32.30s
% Output     : Refutation 32.30s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 384 expanded)
%              Number of leaves         :   47 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          : 1214 (7850 expanded)
%              Number of equality atoms :   77 ( 472 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ sk_B ) )
      = ( k1_relat_1 @ sk_E ) )
    | ~ ( v2_funct_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_E )
      = ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('33',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('36',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['18','31','32','33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['49','58'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['49','58'])).

thf('72',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['63','70','71','72','75'])).

thf('77',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['36','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('84',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('86',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('89',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('93',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k9_relat_1 @ X7 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('94',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['49','58'])).

thf('95',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('97',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('98',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['92','98'])).

thf('100',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['77','99'])).

thf('101',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('104',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['101','104'])).

thf('106',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tYSDv5vPMK
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 32.30/32.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 32.30/32.54  % Solved by: fo/fo7.sh
% 32.30/32.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.30/32.54  % done 11294 iterations in 32.070s
% 32.30/32.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 32.30/32.54  % SZS output start Refutation
% 32.30/32.54  thf(sk_B_type, type, sk_B: $i).
% 32.30/32.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 32.30/32.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 32.30/32.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 32.30/32.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 32.30/32.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 32.30/32.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 32.30/32.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 32.30/32.54  thf(sk_D_type, type, sk_D: $i).
% 32.30/32.54  thf(sk_A_type, type, sk_A: $i).
% 32.30/32.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 32.30/32.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 32.30/32.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 32.30/32.54  thf(sk_C_type, type, sk_C: $i).
% 32.30/32.54  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 32.30/32.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 32.30/32.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 32.30/32.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 32.30/32.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.30/32.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 32.30/32.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 32.30/32.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 32.30/32.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 32.30/32.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.30/32.54  thf(sk_E_type, type, sk_E: $i).
% 32.30/32.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 32.30/32.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 32.30/32.54  thf(t28_funct_2, conjecture,
% 32.30/32.54    (![A:$i,B:$i,C:$i,D:$i]:
% 32.30/32.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 32.30/32.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.30/32.54       ( ![E:$i]:
% 32.30/32.54         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 32.30/32.54             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 32.30/32.54           ( ( ( ( k2_relset_1 @
% 32.30/32.54                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 32.30/32.54                 ( C ) ) & 
% 32.30/32.54               ( v2_funct_1 @ E ) ) =>
% 32.30/32.54             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 32.30/32.54               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 32.30/32.54  thf(zf_stmt_0, negated_conjecture,
% 32.30/32.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 32.30/32.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 32.30/32.54            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.30/32.54          ( ![E:$i]:
% 32.30/32.54            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 32.30/32.54                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 32.30/32.54              ( ( ( ( k2_relset_1 @
% 32.30/32.54                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 32.30/32.54                    ( C ) ) & 
% 32.30/32.54                  ( v2_funct_1 @ E ) ) =>
% 32.30/32.54                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 32.30/32.54                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 32.30/32.54    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 32.30/32.54  thf('0', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf(d1_funct_2, axiom,
% 32.30/32.54    (![A:$i,B:$i,C:$i]:
% 32.30/32.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.30/32.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 32.30/32.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 32.30/32.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 32.30/32.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 32.30/32.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 32.30/32.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 32.30/32.54  thf(zf_stmt_1, axiom,
% 32.30/32.54    (![C:$i,B:$i,A:$i]:
% 32.30/32.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 32.30/32.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 32.30/32.54  thf('1', plain,
% 32.30/32.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 32.30/32.54         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 32.30/32.54          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 32.30/32.54          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 32.30/32.54  thf('2', plain,
% 32.30/32.54      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 32.30/32.54        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 32.30/32.54      inference('sup-', [status(thm)], ['0', '1'])).
% 32.30/32.54  thf(zf_stmt_2, axiom,
% 32.30/32.54    (![B:$i,A:$i]:
% 32.30/32.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 32.30/32.54       ( zip_tseitin_0 @ B @ A ) ))).
% 32.30/32.54  thf('3', plain,
% 32.30/32.54      (![X27 : $i, X28 : $i]:
% 32.30/32.54         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 32.30/32.54  thf('4', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 32.30/32.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 32.30/32.54  thf(zf_stmt_5, axiom,
% 32.30/32.54    (![A:$i,B:$i,C:$i]:
% 32.30/32.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.30/32.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 32.30/32.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 32.30/32.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 32.30/32.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 32.30/32.54  thf('5', plain,
% 32.30/32.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 32.30/32.54         (~ (zip_tseitin_0 @ X32 @ X33)
% 32.30/32.54          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 32.30/32.54          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 32.30/32.54  thf('6', plain,
% 32.30/32.54      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 32.30/32.54      inference('sup-', [status(thm)], ['4', '5'])).
% 32.30/32.54  thf('7', plain,
% 32.30/32.54      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 32.30/32.54      inference('sup-', [status(thm)], ['3', '6'])).
% 32.30/32.54  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('9', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 32.30/32.54      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 32.30/32.54  thf('10', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf(redefinition_k1_relset_1, axiom,
% 32.30/32.54    (![A:$i,B:$i,C:$i]:
% 32.30/32.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.30/32.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 32.30/32.54  thf('11', plain,
% 32.30/32.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 32.30/32.54         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 32.30/32.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 32.30/32.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 32.30/32.54  thf('12', plain,
% 32.30/32.54      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 32.30/32.54      inference('sup-', [status(thm)], ['10', '11'])).
% 32.30/32.54  thf('13', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 32.30/32.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 32.30/32.54  thf(d10_xboole_0, axiom,
% 32.30/32.54    (![A:$i,B:$i]:
% 32.30/32.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 32.30/32.54  thf('14', plain,
% 32.30/32.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 32.30/32.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 32.30/32.54  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 32.30/32.54      inference('simplify', [status(thm)], ['14'])).
% 32.30/32.54  thf(t164_funct_1, axiom,
% 32.30/32.54    (![A:$i,B:$i]:
% 32.30/32.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 32.30/32.54       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 32.30/32.54         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 32.30/32.54  thf('16', plain,
% 32.30/32.54      (![X13 : $i, X14 : $i]:
% 32.30/32.54         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 32.30/32.54          | ~ (v2_funct_1 @ X14)
% 32.30/32.54          | ((k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X13)) = (X13))
% 32.30/32.54          | ~ (v1_funct_1 @ X14)
% 32.30/32.54          | ~ (v1_relat_1 @ X14))),
% 32.30/32.54      inference('cnf', [status(esa)], [t164_funct_1])).
% 32.30/32.54  thf('17', plain,
% 32.30/32.54      (![X0 : $i]:
% 32.30/32.54         (~ (v1_relat_1 @ X0)
% 32.30/32.54          | ~ (v1_funct_1 @ X0)
% 32.30/32.54          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 32.30/32.54              = (k1_relat_1 @ X0))
% 32.30/32.54          | ~ (v2_funct_1 @ X0))),
% 32.30/32.54      inference('sup-', [status(thm)], ['15', '16'])).
% 32.30/32.54  thf('18', plain,
% 32.30/32.54      ((((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ sk_B))
% 32.30/32.54          = (k1_relat_1 @ sk_E))
% 32.30/32.54        | ~ (v2_funct_1 @ sk_E)
% 32.30/32.54        | ~ (v1_funct_1 @ sk_E)
% 32.30/32.54        | ~ (v1_relat_1 @ sk_E))),
% 32.30/32.54      inference('sup+', [status(thm)], ['13', '17'])).
% 32.30/32.54  thf('19', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf(cc2_relset_1, axiom,
% 32.30/32.54    (![A:$i,B:$i,C:$i]:
% 32.30/32.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.30/32.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 32.30/32.54  thf('20', plain,
% 32.30/32.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 32.30/32.54         ((v4_relat_1 @ X18 @ X19)
% 32.30/32.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 32.30/32.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 32.30/32.54  thf('21', plain, ((v4_relat_1 @ sk_E @ sk_B)),
% 32.30/32.54      inference('sup-', [status(thm)], ['19', '20'])).
% 32.30/32.54  thf(t209_relat_1, axiom,
% 32.30/32.54    (![A:$i,B:$i]:
% 32.30/32.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 32.30/32.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 32.30/32.54  thf('22', plain,
% 32.30/32.54      (![X9 : $i, X10 : $i]:
% 32.30/32.54         (((X9) = (k7_relat_1 @ X9 @ X10))
% 32.30/32.54          | ~ (v4_relat_1 @ X9 @ X10)
% 32.30/32.54          | ~ (v1_relat_1 @ X9))),
% 32.30/32.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 32.30/32.54  thf('23', plain,
% 32.30/32.54      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_B)))),
% 32.30/32.54      inference('sup-', [status(thm)], ['21', '22'])).
% 32.30/32.54  thf('24', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf(cc1_relset_1, axiom,
% 32.30/32.54    (![A:$i,B:$i,C:$i]:
% 32.30/32.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.30/32.54       ( v1_relat_1 @ C ) ))).
% 32.30/32.54  thf('25', plain,
% 32.30/32.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 32.30/32.54         ((v1_relat_1 @ X15)
% 32.30/32.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 32.30/32.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.30/32.54  thf('26', plain, ((v1_relat_1 @ sk_E)),
% 32.30/32.54      inference('sup-', [status(thm)], ['24', '25'])).
% 32.30/32.54  thf('27', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 32.30/32.54      inference('demod', [status(thm)], ['23', '26'])).
% 32.30/32.54  thf(t148_relat_1, axiom,
% 32.30/32.54    (![A:$i,B:$i]:
% 32.30/32.54     ( ( v1_relat_1 @ B ) =>
% 32.30/32.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 32.30/32.54  thf('28', plain,
% 32.30/32.54      (![X5 : $i, X6 : $i]:
% 32.30/32.54         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 32.30/32.54          | ~ (v1_relat_1 @ X5))),
% 32.30/32.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.30/32.54  thf('29', plain,
% 32.30/32.54      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 32.30/32.54        | ~ (v1_relat_1 @ sk_E))),
% 32.30/32.54      inference('sup+', [status(thm)], ['27', '28'])).
% 32.30/32.54  thf('30', plain, ((v1_relat_1 @ sk_E)),
% 32.30/32.54      inference('sup-', [status(thm)], ['24', '25'])).
% 32.30/32.54  thf('31', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 32.30/32.54      inference('demod', [status(thm)], ['29', '30'])).
% 32.30/32.54  thf('32', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 32.30/32.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 32.30/32.54  thf('33', plain, ((v2_funct_1 @ sk_E)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('35', plain, ((v1_relat_1 @ sk_E)),
% 32.30/32.54      inference('sup-', [status(thm)], ['24', '25'])).
% 32.30/32.54  thf('36', plain, (((k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 32.30/32.54      inference('demod', [status(thm)], ['18', '31', '32', '33', '34', '35'])).
% 32.30/32.54  thf('37', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('38', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf(dt_k1_partfun1, axiom,
% 32.30/32.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 32.30/32.54     ( ( ( v1_funct_1 @ E ) & 
% 32.30/32.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.30/32.54         ( v1_funct_1 @ F ) & 
% 32.30/32.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 32.30/32.54       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 32.30/32.54         ( m1_subset_1 @
% 32.30/32.54           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 32.30/32.54           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 32.30/32.54  thf('39', plain,
% 32.30/32.54      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 32.30/32.54         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 32.30/32.54          | ~ (v1_funct_1 @ X35)
% 32.30/32.54          | ~ (v1_funct_1 @ X38)
% 32.30/32.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 32.30/32.54          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 32.30/32.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 32.30/32.54      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 32.30/32.54  thf('40', plain,
% 32.30/32.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.30/32.54         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 32.30/32.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 32.30/32.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 32.30/32.54          | ~ (v1_funct_1 @ X1)
% 32.30/32.54          | ~ (v1_funct_1 @ sk_D))),
% 32.30/32.54      inference('sup-', [status(thm)], ['38', '39'])).
% 32.30/32.54  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('42', plain,
% 32.30/32.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.30/32.54         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 32.30/32.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 32.30/32.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 32.30/32.54          | ~ (v1_funct_1 @ X1))),
% 32.30/32.54      inference('demod', [status(thm)], ['40', '41'])).
% 32.30/32.54  thf('43', plain,
% 32.30/32.54      ((~ (v1_funct_1 @ sk_E)
% 32.30/32.54        | (m1_subset_1 @ 
% 32.30/32.54           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 32.30/32.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 32.30/32.54      inference('sup-', [status(thm)], ['37', '42'])).
% 32.30/32.54  thf('44', plain, ((v1_funct_1 @ sk_E)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('45', plain,
% 32.30/32.54      ((m1_subset_1 @ 
% 32.30/32.54        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 32.30/32.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 32.30/32.54      inference('demod', [status(thm)], ['43', '44'])).
% 32.30/32.54  thf(redefinition_k2_relset_1, axiom,
% 32.30/32.54    (![A:$i,B:$i,C:$i]:
% 32.30/32.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.30/32.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 32.30/32.54  thf('46', plain,
% 32.30/32.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 32.30/32.54         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 32.30/32.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 32.30/32.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.30/32.54  thf('47', plain,
% 32.30/32.54      (((k2_relset_1 @ sk_A @ sk_C @ 
% 32.30/32.54         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 32.30/32.54         = (k2_relat_1 @ 
% 32.30/32.54            (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 32.30/32.54      inference('sup-', [status(thm)], ['45', '46'])).
% 32.30/32.54  thf('48', plain,
% 32.30/32.54      (((k2_relset_1 @ sk_A @ sk_C @ 
% 32.30/32.54         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('49', plain,
% 32.30/32.54      (((k2_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 32.30/32.54         = (sk_C))),
% 32.30/32.54      inference('sup+', [status(thm)], ['47', '48'])).
% 32.30/32.54  thf('50', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('51', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf(redefinition_k1_partfun1, axiom,
% 32.30/32.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 32.30/32.54     ( ( ( v1_funct_1 @ E ) & 
% 32.30/32.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.30/32.54         ( v1_funct_1 @ F ) & 
% 32.30/32.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 32.30/32.54       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 32.30/32.54  thf('52', plain,
% 32.30/32.54      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 32.30/32.54         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 32.30/32.54          | ~ (v1_funct_1 @ X41)
% 32.30/32.54          | ~ (v1_funct_1 @ X44)
% 32.30/32.54          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 32.30/32.54          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 32.30/32.54              = (k5_relat_1 @ X41 @ X44)))),
% 32.30/32.54      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 32.30/32.54  thf('53', plain,
% 32.30/32.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.30/32.54         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 32.30/32.54            = (k5_relat_1 @ sk_D @ X0))
% 32.30/32.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 32.30/32.54          | ~ (v1_funct_1 @ X0)
% 32.30/32.54          | ~ (v1_funct_1 @ sk_D))),
% 32.30/32.54      inference('sup-', [status(thm)], ['51', '52'])).
% 32.30/32.54  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('55', plain,
% 32.30/32.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.30/32.54         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 32.30/32.54            = (k5_relat_1 @ sk_D @ X0))
% 32.30/32.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 32.30/32.54          | ~ (v1_funct_1 @ X0))),
% 32.30/32.54      inference('demod', [status(thm)], ['53', '54'])).
% 32.30/32.54  thf('56', plain,
% 32.30/32.54      ((~ (v1_funct_1 @ sk_E)
% 32.30/32.54        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 32.30/32.54            = (k5_relat_1 @ sk_D @ sk_E)))),
% 32.30/32.54      inference('sup-', [status(thm)], ['50', '55'])).
% 32.30/32.54  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('58', plain,
% 32.30/32.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 32.30/32.54         = (k5_relat_1 @ sk_D @ sk_E))),
% 32.30/32.54      inference('demod', [status(thm)], ['56', '57'])).
% 32.30/32.54  thf('59', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 32.30/32.54      inference('demod', [status(thm)], ['49', '58'])).
% 32.30/32.54  thf(t45_relat_1, axiom,
% 32.30/32.54    (![A:$i]:
% 32.30/32.54     ( ( v1_relat_1 @ A ) =>
% 32.30/32.54       ( ![B:$i]:
% 32.30/32.54         ( ( v1_relat_1 @ B ) =>
% 32.30/32.54           ( r1_tarski @
% 32.30/32.54             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 32.30/32.54  thf('60', plain,
% 32.30/32.54      (![X11 : $i, X12 : $i]:
% 32.30/32.54         (~ (v1_relat_1 @ X11)
% 32.30/32.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 32.30/32.54             (k2_relat_1 @ X11))
% 32.30/32.54          | ~ (v1_relat_1 @ X12))),
% 32.30/32.54      inference('cnf', [status(esa)], [t45_relat_1])).
% 32.30/32.54  thf('61', plain,
% 32.30/32.54      (![X0 : $i, X2 : $i]:
% 32.30/32.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 32.30/32.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 32.30/32.54  thf('62', plain,
% 32.30/32.54      (![X0 : $i, X1 : $i]:
% 32.30/32.54         (~ (v1_relat_1 @ X1)
% 32.30/32.54          | ~ (v1_relat_1 @ X0)
% 32.30/32.54          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 32.30/32.54               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 32.30/32.54          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 32.30/32.54      inference('sup-', [status(thm)], ['60', '61'])).
% 32.30/32.54  thf('63', plain,
% 32.30/32.54      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 32.30/32.54        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 32.30/32.54        | ~ (v1_relat_1 @ sk_E)
% 32.30/32.54        | ~ (v1_relat_1 @ sk_D))),
% 32.30/32.54      inference('sup-', [status(thm)], ['59', '62'])).
% 32.30/32.54  thf('64', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('65', plain,
% 32.30/32.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 32.30/32.54         ((v5_relat_1 @ X18 @ X20)
% 32.30/32.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 32.30/32.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 32.30/32.54  thf('66', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 32.30/32.54      inference('sup-', [status(thm)], ['64', '65'])).
% 32.30/32.54  thf(d19_relat_1, axiom,
% 32.30/32.54    (![A:$i,B:$i]:
% 32.30/32.54     ( ( v1_relat_1 @ B ) =>
% 32.30/32.54       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 32.30/32.54  thf('67', plain,
% 32.30/32.54      (![X3 : $i, X4 : $i]:
% 32.30/32.54         (~ (v5_relat_1 @ X3 @ X4)
% 32.30/32.54          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 32.30/32.54          | ~ (v1_relat_1 @ X3))),
% 32.30/32.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 32.30/32.54  thf('68', plain,
% 32.30/32.54      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 32.30/32.54      inference('sup-', [status(thm)], ['66', '67'])).
% 32.30/32.54  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 32.30/32.54      inference('sup-', [status(thm)], ['24', '25'])).
% 32.30/32.54  thf('70', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 32.30/32.54      inference('demod', [status(thm)], ['68', '69'])).
% 32.30/32.54  thf('71', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 32.30/32.54      inference('demod', [status(thm)], ['49', '58'])).
% 32.30/32.54  thf('72', plain, ((v1_relat_1 @ sk_E)),
% 32.30/32.54      inference('sup-', [status(thm)], ['24', '25'])).
% 32.30/32.54  thf('73', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('74', plain,
% 32.30/32.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 32.30/32.54         ((v1_relat_1 @ X15)
% 32.30/32.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 32.30/32.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.30/32.54  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 32.30/32.54      inference('sup-', [status(thm)], ['73', '74'])).
% 32.30/32.54  thf('76', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 32.30/32.54      inference('demod', [status(thm)], ['63', '70', '71', '72', '75'])).
% 32.30/32.54  thf('77', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 32.30/32.54      inference('demod', [status(thm)], ['36', '76'])).
% 32.30/32.54  thf('78', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('79', plain,
% 32.30/32.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 32.30/32.54         ((v5_relat_1 @ X18 @ X20)
% 32.30/32.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 32.30/32.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 32.30/32.54  thf('80', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 32.30/32.54      inference('sup-', [status(thm)], ['78', '79'])).
% 32.30/32.54  thf('81', plain,
% 32.30/32.54      (![X3 : $i, X4 : $i]:
% 32.30/32.54         (~ (v5_relat_1 @ X3 @ X4)
% 32.30/32.54          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 32.30/32.54          | ~ (v1_relat_1 @ X3))),
% 32.30/32.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 32.30/32.54  thf('82', plain,
% 32.30/32.54      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 32.30/32.54      inference('sup-', [status(thm)], ['80', '81'])).
% 32.30/32.54  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 32.30/32.54      inference('sup-', [status(thm)], ['73', '74'])).
% 32.30/32.54  thf('84', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 32.30/32.54      inference('demod', [status(thm)], ['82', '83'])).
% 32.30/32.54  thf('85', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 32.30/32.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 32.30/32.54  thf('86', plain,
% 32.30/32.54      (![X13 : $i, X14 : $i]:
% 32.30/32.54         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 32.30/32.54          | ~ (v2_funct_1 @ X14)
% 32.30/32.54          | ((k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X13)) = (X13))
% 32.30/32.54          | ~ (v1_funct_1 @ X14)
% 32.30/32.54          | ~ (v1_relat_1 @ X14))),
% 32.30/32.54      inference('cnf', [status(esa)], [t164_funct_1])).
% 32.30/32.54  thf('87', plain,
% 32.30/32.54      (![X0 : $i]:
% 32.30/32.54         (~ (r1_tarski @ X0 @ sk_B)
% 32.30/32.54          | ~ (v1_relat_1 @ sk_E)
% 32.30/32.54          | ~ (v1_funct_1 @ sk_E)
% 32.30/32.54          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 32.30/32.54          | ~ (v2_funct_1 @ sk_E))),
% 32.30/32.54      inference('sup-', [status(thm)], ['85', '86'])).
% 32.30/32.54  thf('88', plain, ((v1_relat_1 @ sk_E)),
% 32.30/32.54      inference('sup-', [status(thm)], ['24', '25'])).
% 32.30/32.54  thf('89', plain, ((v1_funct_1 @ sk_E)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('90', plain, ((v2_funct_1 @ sk_E)),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('91', plain,
% 32.30/32.54      (![X0 : $i]:
% 32.30/32.54         (~ (r1_tarski @ X0 @ sk_B)
% 32.30/32.54          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 32.30/32.54      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 32.30/32.54  thf('92', plain,
% 32.30/32.54      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 32.30/32.54         = (k2_relat_1 @ sk_D))),
% 32.30/32.54      inference('sup-', [status(thm)], ['84', '91'])).
% 32.30/32.54  thf(t160_relat_1, axiom,
% 32.30/32.54    (![A:$i]:
% 32.30/32.54     ( ( v1_relat_1 @ A ) =>
% 32.30/32.54       ( ![B:$i]:
% 32.30/32.54         ( ( v1_relat_1 @ B ) =>
% 32.30/32.54           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 32.30/32.54             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 32.30/32.54  thf('93', plain,
% 32.30/32.54      (![X7 : $i, X8 : $i]:
% 32.30/32.54         (~ (v1_relat_1 @ X7)
% 32.30/32.54          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 32.30/32.54              = (k9_relat_1 @ X7 @ (k2_relat_1 @ X8)))
% 32.30/32.54          | ~ (v1_relat_1 @ X8))),
% 32.30/32.54      inference('cnf', [status(esa)], [t160_relat_1])).
% 32.30/32.54  thf('94', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 32.30/32.54      inference('demod', [status(thm)], ['49', '58'])).
% 32.30/32.54  thf('95', plain,
% 32.30/32.54      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 32.30/32.54        | ~ (v1_relat_1 @ sk_D)
% 32.30/32.54        | ~ (v1_relat_1 @ sk_E))),
% 32.30/32.54      inference('sup+', [status(thm)], ['93', '94'])).
% 32.30/32.54  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 32.30/32.54      inference('sup-', [status(thm)], ['73', '74'])).
% 32.30/32.54  thf('97', plain, ((v1_relat_1 @ sk_E)),
% 32.30/32.54      inference('sup-', [status(thm)], ['24', '25'])).
% 32.30/32.54  thf('98', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 32.30/32.54      inference('demod', [status(thm)], ['95', '96', '97'])).
% 32.30/32.54  thf('99', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 32.30/32.54      inference('demod', [status(thm)], ['92', '98'])).
% 32.30/32.54  thf('100', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 32.30/32.54      inference('sup+', [status(thm)], ['77', '99'])).
% 32.30/32.54  thf('101', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('102', plain,
% 32.30/32.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.30/32.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.30/32.54  thf('103', plain,
% 32.30/32.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 32.30/32.54         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 32.30/32.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 32.30/32.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.30/32.54  thf('104', plain,
% 32.30/32.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 32.30/32.54      inference('sup-', [status(thm)], ['102', '103'])).
% 32.30/32.54  thf('105', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 32.30/32.54      inference('demod', [status(thm)], ['101', '104'])).
% 32.30/32.54  thf('106', plain, ($false),
% 32.30/32.54      inference('simplify_reflect-', [status(thm)], ['100', '105'])).
% 32.30/32.54  
% 32.30/32.54  % SZS output end Refutation
% 32.30/32.54  
% 32.30/32.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
