%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AuZdt8Rcfl

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:59 EST 2020

% Result     : Theorem 3.48s
% Output     : Refutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 475 expanded)
%              Number of leaves         :   46 ( 159 expanded)
%              Depth                    :   14
%              Number of atoms          : 1192 (9737 expanded)
%              Number of equality atoms :   76 ( 586 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k10_relat_1 @ X15 @ ( k9_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf('19',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('20',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','20','21','26'])).

thf('28',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('30',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_B )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['24','25'])).

thf('32',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41','50'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['53','56'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('65',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['24','25'])).

thf('68',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['53','56'])).

thf('70',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['24','25'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['61','68','69','70','75'])).

thf('77',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['33','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['73','74'])).

thf('84',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k10_relat_1 @ X15 @ ( k9_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    inference(demod,[status(thm)],['24','25'])).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k9_relat_1 @ X10 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('94',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['53','56'])).

thf('95',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['73','74'])).

thf('97',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['24','25'])).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AuZdt8Rcfl
% 0.12/0.36  % Computer   : n025.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 16:37:21 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 3.48/3.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.48/3.66  % Solved by: fo/fo7.sh
% 3.48/3.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.48/3.66  % done 1092 iterations in 3.223s
% 3.48/3.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.48/3.66  % SZS output start Refutation
% 3.48/3.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.48/3.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.48/3.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.48/3.66  thf(sk_C_type, type, sk_C: $i).
% 3.48/3.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.48/3.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.48/3.66  thf(sk_B_type, type, sk_B: $i).
% 3.48/3.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.48/3.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.48/3.66  thf(sk_D_type, type, sk_D: $i).
% 3.48/3.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.48/3.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.48/3.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.48/3.66  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.48/3.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.48/3.66  thf(sk_A_type, type, sk_A: $i).
% 3.48/3.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.48/3.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.48/3.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.48/3.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.48/3.66  thf(sk_E_type, type, sk_E: $i).
% 3.48/3.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.48/3.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.48/3.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.48/3.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.48/3.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.48/3.66  thf(t28_funct_2, conjecture,
% 3.48/3.66    (![A:$i,B:$i,C:$i,D:$i]:
% 3.48/3.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.48/3.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.48/3.66       ( ![E:$i]:
% 3.48/3.66         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.48/3.66             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.48/3.66           ( ( ( ( k2_relset_1 @
% 3.48/3.66                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.48/3.66                 ( C ) ) & 
% 3.48/3.66               ( v2_funct_1 @ E ) ) =>
% 3.48/3.66             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.48/3.66               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 3.48/3.66  thf(zf_stmt_0, negated_conjecture,
% 3.48/3.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.48/3.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.48/3.66            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.48/3.66          ( ![E:$i]:
% 3.48/3.66            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.48/3.66                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.48/3.66              ( ( ( ( k2_relset_1 @
% 3.48/3.66                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.48/3.66                    ( C ) ) & 
% 3.48/3.66                  ( v2_funct_1 @ E ) ) =>
% 3.48/3.66                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.48/3.66                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 3.48/3.66    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 3.48/3.66  thf('0', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf(d1_funct_2, axiom,
% 3.48/3.66    (![A:$i,B:$i,C:$i]:
% 3.48/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.48/3.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.48/3.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.48/3.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.48/3.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.48/3.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.48/3.66  thf(zf_stmt_1, axiom,
% 3.48/3.66    (![C:$i,B:$i,A:$i]:
% 3.48/3.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.48/3.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.48/3.66  thf('1', plain,
% 3.48/3.66      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.48/3.66         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 3.48/3.66          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 3.48/3.66          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.48/3.66  thf('2', plain,
% 3.48/3.66      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 3.48/3.66        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 3.48/3.66      inference('sup-', [status(thm)], ['0', '1'])).
% 3.48/3.66  thf(zf_stmt_2, axiom,
% 3.48/3.66    (![B:$i,A:$i]:
% 3.48/3.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.48/3.66       ( zip_tseitin_0 @ B @ A ) ))).
% 3.48/3.66  thf('3', plain,
% 3.48/3.66      (![X25 : $i, X26 : $i]:
% 3.48/3.66         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.48/3.66  thf('4', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.48/3.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.48/3.66  thf(zf_stmt_5, axiom,
% 3.48/3.66    (![A:$i,B:$i,C:$i]:
% 3.48/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.48/3.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.48/3.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.48/3.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.48/3.66  thf('5', plain,
% 3.48/3.66      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.48/3.66         (~ (zip_tseitin_0 @ X30 @ X31)
% 3.48/3.66          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 3.48/3.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.48/3.66  thf('6', plain,
% 3.48/3.66      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.48/3.66      inference('sup-', [status(thm)], ['4', '5'])).
% 3.48/3.66  thf('7', plain,
% 3.48/3.66      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 3.48/3.66      inference('sup-', [status(thm)], ['3', '6'])).
% 3.48/3.66  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('9', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 3.48/3.66      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 3.48/3.66  thf('10', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf(redefinition_k1_relset_1, axiom,
% 3.48/3.66    (![A:$i,B:$i,C:$i]:
% 3.48/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.48/3.66  thf('11', plain,
% 3.48/3.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.48/3.66         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 3.48/3.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.48/3.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.48/3.66  thf('12', plain,
% 3.48/3.66      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.48/3.66      inference('sup-', [status(thm)], ['10', '11'])).
% 3.48/3.66  thf('13', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.48/3.66      inference('demod', [status(thm)], ['2', '9', '12'])).
% 3.48/3.66  thf(d10_xboole_0, axiom,
% 3.48/3.66    (![A:$i,B:$i]:
% 3.48/3.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.48/3.66  thf('14', plain,
% 3.48/3.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.48/3.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.48/3.66  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.48/3.66      inference('simplify', [status(thm)], ['14'])).
% 3.48/3.66  thf(t164_funct_1, axiom,
% 3.48/3.66    (![A:$i,B:$i]:
% 3.48/3.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.48/3.66       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 3.48/3.66         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.48/3.66  thf('16', plain,
% 3.48/3.66      (![X14 : $i, X15 : $i]:
% 3.48/3.66         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 3.48/3.66          | ~ (v2_funct_1 @ X15)
% 3.48/3.66          | ((k10_relat_1 @ X15 @ (k9_relat_1 @ X15 @ X14)) = (X14))
% 3.48/3.66          | ~ (v1_funct_1 @ X15)
% 3.48/3.66          | ~ (v1_relat_1 @ X15))),
% 3.48/3.66      inference('cnf', [status(esa)], [t164_funct_1])).
% 3.48/3.66  thf('17', plain,
% 3.48/3.66      (![X0 : $i]:
% 3.48/3.66         (~ (v1_relat_1 @ X0)
% 3.48/3.66          | ~ (v1_funct_1 @ X0)
% 3.48/3.66          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.48/3.66              = (k1_relat_1 @ X0))
% 3.48/3.66          | ~ (v2_funct_1 @ X0))),
% 3.48/3.66      inference('sup-', [status(thm)], ['15', '16'])).
% 3.48/3.66  thf('18', plain,
% 3.48/3.66      ((((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ sk_B))
% 3.48/3.66          = (k1_relat_1 @ sk_E))
% 3.48/3.66        | ~ (v2_funct_1 @ sk_E)
% 3.48/3.66        | ~ (v1_funct_1 @ sk_E)
% 3.48/3.66        | ~ (v1_relat_1 @ sk_E))),
% 3.48/3.66      inference('sup+', [status(thm)], ['13', '17'])).
% 3.48/3.66  thf('19', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.48/3.66      inference('demod', [status(thm)], ['2', '9', '12'])).
% 3.48/3.66  thf('20', plain, ((v2_funct_1 @ sk_E)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('22', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf(cc2_relat_1, axiom,
% 3.48/3.66    (![A:$i]:
% 3.48/3.66     ( ( v1_relat_1 @ A ) =>
% 3.48/3.66       ( ![B:$i]:
% 3.48/3.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.48/3.66  thf('23', plain,
% 3.48/3.66      (![X3 : $i, X4 : $i]:
% 3.48/3.66         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.48/3.66          | (v1_relat_1 @ X3)
% 3.48/3.66          | ~ (v1_relat_1 @ X4))),
% 3.48/3.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.48/3.66  thf('24', plain,
% 3.48/3.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 3.48/3.66      inference('sup-', [status(thm)], ['22', '23'])).
% 3.48/3.66  thf(fc6_relat_1, axiom,
% 3.48/3.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.48/3.66  thf('25', plain,
% 3.48/3.66      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 3.48/3.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.48/3.66  thf('26', plain, ((v1_relat_1 @ sk_E)),
% 3.48/3.66      inference('demod', [status(thm)], ['24', '25'])).
% 3.48/3.66  thf('27', plain,
% 3.48/3.66      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 3.48/3.66      inference('demod', [status(thm)], ['18', '19', '20', '21', '26'])).
% 3.48/3.66  thf('28', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.48/3.66      inference('demod', [status(thm)], ['2', '9', '12'])).
% 3.48/3.66  thf(t146_relat_1, axiom,
% 3.48/3.66    (![A:$i]:
% 3.48/3.66     ( ( v1_relat_1 @ A ) =>
% 3.48/3.66       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 3.48/3.66  thf('29', plain,
% 3.48/3.66      (![X9 : $i]:
% 3.48/3.66         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 3.48/3.66          | ~ (v1_relat_1 @ X9))),
% 3.48/3.66      inference('cnf', [status(esa)], [t146_relat_1])).
% 3.48/3.66  thf('30', plain,
% 3.48/3.66      ((((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))
% 3.48/3.66        | ~ (v1_relat_1 @ sk_E))),
% 3.48/3.66      inference('sup+', [status(thm)], ['28', '29'])).
% 3.48/3.66  thf('31', plain, ((v1_relat_1 @ sk_E)),
% 3.48/3.66      inference('demod', [status(thm)], ['24', '25'])).
% 3.48/3.66  thf('32', plain, (((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))),
% 3.48/3.66      inference('demod', [status(thm)], ['30', '31'])).
% 3.48/3.66  thf('33', plain, (((k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 3.48/3.66      inference('demod', [status(thm)], ['27', '32'])).
% 3.48/3.66  thf('34', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('35', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf(dt_k1_partfun1, axiom,
% 3.48/3.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.48/3.66     ( ( ( v1_funct_1 @ E ) & 
% 3.48/3.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.48/3.66         ( v1_funct_1 @ F ) & 
% 3.48/3.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.48/3.66       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.48/3.66         ( m1_subset_1 @
% 3.48/3.66           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.48/3.66           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.48/3.66  thf('36', plain,
% 3.48/3.66      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.48/3.66         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.48/3.66          | ~ (v1_funct_1 @ X33)
% 3.48/3.66          | ~ (v1_funct_1 @ X36)
% 3.48/3.66          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.48/3.66          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 3.48/3.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 3.48/3.66      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.48/3.66  thf('37', plain,
% 3.48/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.48/3.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 3.48/3.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.48/3.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.48/3.66          | ~ (v1_funct_1 @ X1)
% 3.48/3.66          | ~ (v1_funct_1 @ sk_D))),
% 3.48/3.66      inference('sup-', [status(thm)], ['35', '36'])).
% 3.48/3.66  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('39', plain,
% 3.48/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.48/3.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 3.48/3.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.48/3.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.48/3.66          | ~ (v1_funct_1 @ X1))),
% 3.48/3.66      inference('demod', [status(thm)], ['37', '38'])).
% 3.48/3.66  thf('40', plain,
% 3.48/3.66      ((~ (v1_funct_1 @ sk_E)
% 3.48/3.66        | (m1_subset_1 @ 
% 3.48/3.66           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 3.48/3.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 3.48/3.66      inference('sup-', [status(thm)], ['34', '39'])).
% 3.48/3.66  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('42', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('43', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf(redefinition_k1_partfun1, axiom,
% 3.48/3.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.48/3.66     ( ( ( v1_funct_1 @ E ) & 
% 3.48/3.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.48/3.66         ( v1_funct_1 @ F ) & 
% 3.48/3.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.48/3.66       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.48/3.66  thf('44', plain,
% 3.48/3.66      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.48/3.66         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.48/3.66          | ~ (v1_funct_1 @ X39)
% 3.48/3.66          | ~ (v1_funct_1 @ X42)
% 3.48/3.66          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.48/3.66          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 3.48/3.66              = (k5_relat_1 @ X39 @ X42)))),
% 3.48/3.66      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.48/3.66  thf('45', plain,
% 3.48/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.48/3.66         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.48/3.66            = (k5_relat_1 @ sk_D @ X0))
% 3.48/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.48/3.66          | ~ (v1_funct_1 @ X0)
% 3.48/3.66          | ~ (v1_funct_1 @ sk_D))),
% 3.48/3.66      inference('sup-', [status(thm)], ['43', '44'])).
% 3.48/3.66  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('47', plain,
% 3.48/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.48/3.66         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 3.48/3.66            = (k5_relat_1 @ sk_D @ X0))
% 3.48/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.48/3.66          | ~ (v1_funct_1 @ X0))),
% 3.48/3.66      inference('demod', [status(thm)], ['45', '46'])).
% 3.48/3.66  thf('48', plain,
% 3.48/3.66      ((~ (v1_funct_1 @ sk_E)
% 3.48/3.66        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.48/3.66            = (k5_relat_1 @ sk_D @ sk_E)))),
% 3.48/3.66      inference('sup-', [status(thm)], ['42', '47'])).
% 3.48/3.66  thf('49', plain, ((v1_funct_1 @ sk_E)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('50', plain,
% 3.48/3.66      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.48/3.66         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.48/3.66      inference('demod', [status(thm)], ['48', '49'])).
% 3.48/3.66  thf('51', plain,
% 3.48/3.66      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 3.48/3.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.48/3.66      inference('demod', [status(thm)], ['40', '41', '50'])).
% 3.48/3.66  thf(redefinition_k2_relset_1, axiom,
% 3.48/3.66    (![A:$i,B:$i,C:$i]:
% 3.48/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.48/3.66  thf('52', plain,
% 3.48/3.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.48/3.66         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 3.48/3.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.48/3.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.48/3.66  thf('53', plain,
% 3.48/3.66      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 3.48/3.66         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 3.48/3.66      inference('sup-', [status(thm)], ['51', '52'])).
% 3.48/3.66  thf('54', plain,
% 3.48/3.66      (((k2_relset_1 @ sk_A @ sk_C @ 
% 3.48/3.66         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('55', plain,
% 3.48/3.66      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 3.48/3.66         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.48/3.66      inference('demod', [status(thm)], ['48', '49'])).
% 3.48/3.66  thf('56', plain,
% 3.48/3.66      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.48/3.66      inference('demod', [status(thm)], ['54', '55'])).
% 3.48/3.66  thf('57', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.48/3.66      inference('sup+', [status(thm)], ['53', '56'])).
% 3.48/3.66  thf(t45_relat_1, axiom,
% 3.48/3.66    (![A:$i]:
% 3.48/3.66     ( ( v1_relat_1 @ A ) =>
% 3.48/3.66       ( ![B:$i]:
% 3.48/3.66         ( ( v1_relat_1 @ B ) =>
% 3.48/3.66           ( r1_tarski @
% 3.48/3.66             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.48/3.66  thf('58', plain,
% 3.48/3.66      (![X12 : $i, X13 : $i]:
% 3.48/3.66         (~ (v1_relat_1 @ X12)
% 3.48/3.66          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 3.48/3.66             (k2_relat_1 @ X12))
% 3.48/3.66          | ~ (v1_relat_1 @ X13))),
% 3.48/3.66      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.48/3.66  thf('59', plain,
% 3.48/3.66      (![X0 : $i, X2 : $i]:
% 3.48/3.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.48/3.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.48/3.66  thf('60', plain,
% 3.48/3.66      (![X0 : $i, X1 : $i]:
% 3.48/3.66         (~ (v1_relat_1 @ X1)
% 3.48/3.66          | ~ (v1_relat_1 @ X0)
% 3.48/3.66          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 3.48/3.66               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.48/3.66          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 3.48/3.66      inference('sup-', [status(thm)], ['58', '59'])).
% 3.48/3.66  thf('61', plain,
% 3.48/3.66      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 3.48/3.66        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 3.48/3.66        | ~ (v1_relat_1 @ sk_E)
% 3.48/3.66        | ~ (v1_relat_1 @ sk_D))),
% 3.48/3.66      inference('sup-', [status(thm)], ['57', '60'])).
% 3.48/3.66  thf('62', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf(cc2_relset_1, axiom,
% 3.48/3.66    (![A:$i,B:$i,C:$i]:
% 3.48/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.48/3.66  thf('63', plain,
% 3.48/3.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.48/3.66         ((v5_relat_1 @ X16 @ X18)
% 3.48/3.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.48/3.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.48/3.66  thf('64', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 3.48/3.66      inference('sup-', [status(thm)], ['62', '63'])).
% 3.48/3.66  thf(d19_relat_1, axiom,
% 3.48/3.66    (![A:$i,B:$i]:
% 3.48/3.66     ( ( v1_relat_1 @ B ) =>
% 3.48/3.66       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.48/3.66  thf('65', plain,
% 3.48/3.66      (![X5 : $i, X6 : $i]:
% 3.48/3.66         (~ (v5_relat_1 @ X5 @ X6)
% 3.48/3.66          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 3.48/3.66          | ~ (v1_relat_1 @ X5))),
% 3.48/3.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.48/3.66  thf('66', plain,
% 3.48/3.66      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 3.48/3.66      inference('sup-', [status(thm)], ['64', '65'])).
% 3.48/3.66  thf('67', plain, ((v1_relat_1 @ sk_E)),
% 3.48/3.66      inference('demod', [status(thm)], ['24', '25'])).
% 3.48/3.66  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 3.48/3.66      inference('demod', [status(thm)], ['66', '67'])).
% 3.48/3.66  thf('69', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.48/3.66      inference('sup+', [status(thm)], ['53', '56'])).
% 3.48/3.66  thf('70', plain, ((v1_relat_1 @ sk_E)),
% 3.48/3.66      inference('demod', [status(thm)], ['24', '25'])).
% 3.48/3.66  thf('71', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('72', plain,
% 3.48/3.66      (![X3 : $i, X4 : $i]:
% 3.48/3.66         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.48/3.66          | (v1_relat_1 @ X3)
% 3.48/3.66          | ~ (v1_relat_1 @ X4))),
% 3.48/3.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.48/3.66  thf('73', plain,
% 3.48/3.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 3.48/3.66      inference('sup-', [status(thm)], ['71', '72'])).
% 3.48/3.66  thf('74', plain,
% 3.48/3.66      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 3.48/3.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.48/3.66  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 3.48/3.66      inference('demod', [status(thm)], ['73', '74'])).
% 3.48/3.66  thf('76', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 3.48/3.66      inference('demod', [status(thm)], ['61', '68', '69', '70', '75'])).
% 3.48/3.66  thf('77', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 3.48/3.66      inference('demod', [status(thm)], ['33', '76'])).
% 3.48/3.66  thf('78', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('79', plain,
% 3.48/3.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.48/3.66         ((v5_relat_1 @ X16 @ X18)
% 3.48/3.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.48/3.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.48/3.66  thf('80', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 3.48/3.66      inference('sup-', [status(thm)], ['78', '79'])).
% 3.48/3.66  thf('81', plain,
% 3.48/3.66      (![X5 : $i, X6 : $i]:
% 3.48/3.66         (~ (v5_relat_1 @ X5 @ X6)
% 3.48/3.66          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 3.48/3.66          | ~ (v1_relat_1 @ X5))),
% 3.48/3.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.48/3.66  thf('82', plain,
% 3.48/3.66      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 3.48/3.66      inference('sup-', [status(thm)], ['80', '81'])).
% 3.48/3.66  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 3.48/3.66      inference('demod', [status(thm)], ['73', '74'])).
% 3.48/3.66  thf('84', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 3.48/3.66      inference('demod', [status(thm)], ['82', '83'])).
% 3.48/3.66  thf('85', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 3.48/3.66      inference('demod', [status(thm)], ['2', '9', '12'])).
% 3.48/3.66  thf('86', plain,
% 3.48/3.66      (![X14 : $i, X15 : $i]:
% 3.48/3.66         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 3.48/3.66          | ~ (v2_funct_1 @ X15)
% 3.48/3.66          | ((k10_relat_1 @ X15 @ (k9_relat_1 @ X15 @ X14)) = (X14))
% 3.48/3.66          | ~ (v1_funct_1 @ X15)
% 3.48/3.66          | ~ (v1_relat_1 @ X15))),
% 3.48/3.66      inference('cnf', [status(esa)], [t164_funct_1])).
% 3.48/3.66  thf('87', plain,
% 3.48/3.66      (![X0 : $i]:
% 3.48/3.66         (~ (r1_tarski @ X0 @ sk_B)
% 3.48/3.66          | ~ (v1_relat_1 @ sk_E)
% 3.48/3.66          | ~ (v1_funct_1 @ sk_E)
% 3.48/3.66          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 3.48/3.66          | ~ (v2_funct_1 @ sk_E))),
% 3.48/3.66      inference('sup-', [status(thm)], ['85', '86'])).
% 3.48/3.66  thf('88', plain, ((v1_relat_1 @ sk_E)),
% 3.48/3.66      inference('demod', [status(thm)], ['24', '25'])).
% 3.48/3.66  thf('89', plain, ((v1_funct_1 @ sk_E)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('90', plain, ((v2_funct_1 @ sk_E)),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('91', plain,
% 3.48/3.66      (![X0 : $i]:
% 3.48/3.66         (~ (r1_tarski @ X0 @ sk_B)
% 3.48/3.66          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 3.48/3.66      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 3.48/3.66  thf('92', plain,
% 3.48/3.66      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 3.48/3.66         = (k2_relat_1 @ sk_D))),
% 3.48/3.66      inference('sup-', [status(thm)], ['84', '91'])).
% 3.48/3.66  thf(t160_relat_1, axiom,
% 3.48/3.66    (![A:$i]:
% 3.48/3.66     ( ( v1_relat_1 @ A ) =>
% 3.48/3.66       ( ![B:$i]:
% 3.48/3.66         ( ( v1_relat_1 @ B ) =>
% 3.48/3.66           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 3.48/3.66             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.48/3.66  thf('93', plain,
% 3.48/3.66      (![X10 : $i, X11 : $i]:
% 3.48/3.66         (~ (v1_relat_1 @ X10)
% 3.48/3.66          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 3.48/3.66              = (k9_relat_1 @ X10 @ (k2_relat_1 @ X11)))
% 3.48/3.66          | ~ (v1_relat_1 @ X11))),
% 3.48/3.66      inference('cnf', [status(esa)], [t160_relat_1])).
% 3.48/3.66  thf('94', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 3.48/3.66      inference('sup+', [status(thm)], ['53', '56'])).
% 3.48/3.66  thf('95', plain,
% 3.48/3.66      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 3.48/3.66        | ~ (v1_relat_1 @ sk_D)
% 3.48/3.66        | ~ (v1_relat_1 @ sk_E))),
% 3.48/3.66      inference('sup+', [status(thm)], ['93', '94'])).
% 3.48/3.66  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 3.48/3.66      inference('demod', [status(thm)], ['73', '74'])).
% 3.48/3.66  thf('97', plain, ((v1_relat_1 @ sk_E)),
% 3.48/3.66      inference('demod', [status(thm)], ['24', '25'])).
% 3.48/3.66  thf('98', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 3.48/3.66      inference('demod', [status(thm)], ['95', '96', '97'])).
% 3.48/3.66  thf('99', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 3.48/3.66      inference('demod', [status(thm)], ['92', '98'])).
% 3.48/3.66  thf('100', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 3.48/3.66      inference('sup+', [status(thm)], ['77', '99'])).
% 3.48/3.66  thf('101', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('102', plain,
% 3.48/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.48/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.66  thf('103', plain,
% 3.48/3.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.48/3.66         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 3.48/3.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.48/3.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.48/3.66  thf('104', plain,
% 3.48/3.66      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.48/3.66      inference('sup-', [status(thm)], ['102', '103'])).
% 3.48/3.66  thf('105', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 3.48/3.66      inference('demod', [status(thm)], ['101', '104'])).
% 3.48/3.66  thf('106', plain, ($false),
% 3.48/3.66      inference('simplify_reflect-', [status(thm)], ['100', '105'])).
% 3.48/3.66  
% 3.48/3.66  % SZS output end Refutation
% 3.48/3.66  
% 3.51/3.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
