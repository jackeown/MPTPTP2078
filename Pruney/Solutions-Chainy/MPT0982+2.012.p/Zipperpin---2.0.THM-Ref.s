%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sdYvINP6nQ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:56 EST 2020

% Result     : Theorem 46.48s
% Output     : Refutation 46.48s
% Verified   : 
% Statistics : Number of formulae       :  243 (1048 expanded)
%              Number of leaves         :   49 ( 332 expanded)
%              Depth                    :   25
%              Number of atoms          : 2220 (19438 expanded)
%              Number of equality atoms :  144 (1174 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k9_relat_1 @ X13 @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ sk_A ) @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_D @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('25',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X9 @ X10 ) @ ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ ( k9_relat_1 @ sk_E @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v4_relat_1 @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('54',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_E )
      = ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ ( k2_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['46','59','60'])).

thf('62',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['30','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('64',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t120_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
          = A ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X5 @ ( k2_relat_1 @ X6 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t120_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_E ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k7_relat_1 @ sk_E @ sk_B ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('71',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('72',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('73',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_E ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_E ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','29'])).

thf('77',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X9 @ X10 ) @ ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X0 @ X1 ) @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ X0 @ X1 ) @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_E @ X0 ) @ ( k7_relat_1 @ sk_E @ ( k1_relat_1 @ sk_E ) ) ) )
        = ( k9_relat_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('84',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('85',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('86',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf('87',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_E @ X0 ) @ sk_E ) )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87'])).

thf('89',plain,
    ( ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ sk_E ) )
      = ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['76','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('91',plain,
    ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ sk_E ) )
    = ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['75','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
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

thf('103',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['99','100','109'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('111',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('112',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('115',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,
    ( sk_C
    = ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['92','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('119',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['118'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('120',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k8_relat_1 @ X8 @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('126',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('128',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('129',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X5 @ ( k2_relat_1 @ X6 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t120_relat_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X5 @ ( k2_relat_1 @ X6 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t120_relat_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','134'])).

thf('136',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k9_relat_1 @ X13 @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['125','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['124','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['123','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('144',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X17 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) )
       != ( k2_relat_1 @ X18 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
       != ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['121','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( k2_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_D ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['117','150'])).

thf('152',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('153',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('154',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['112','115'])).

thf('156',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('158',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('160',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('162',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['112','115'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['154','155','162','163'])).

thf('165',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('167',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('168',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf('171',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('173',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('174',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k8_relat_1 @ X8 @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( ( k8_relat_1 @ X0 @ ( k7_relat_1 @ sk_D @ sk_A ) )
        = ( k7_relat_1 @ sk_D @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('178',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('179',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('180',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('181',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( ( k8_relat_1 @ X0 @ sk_D )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180','181'])).

thf('183',plain,
    ( ( k8_relat_1 @ ( k2_relat_1 @ sk_D ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['171','182'])).

thf('184',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['151','164','165','166','167','168','169','170','183'])).

thf('185',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['10','185'])).

thf('187',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('190',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['187','190'])).

thf('192',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['186','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sdYvINP6nQ
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:45:03 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 46.48/46.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 46.48/46.73  % Solved by: fo/fo7.sh
% 46.48/46.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 46.48/46.73  % done 7669 iterations in 46.289s
% 46.48/46.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 46.48/46.73  % SZS output start Refutation
% 46.48/46.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 46.48/46.73  thf(sk_B_type, type, sk_B: $i).
% 46.48/46.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 46.48/46.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 46.48/46.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 46.48/46.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 46.48/46.73  thf(sk_E_type, type, sk_E: $i).
% 46.48/46.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 46.48/46.73  thf(sk_D_type, type, sk_D: $i).
% 46.48/46.73  thf(sk_C_type, type, sk_C: $i).
% 46.48/46.73  thf(sk_A_type, type, sk_A: $i).
% 46.48/46.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 46.48/46.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 46.48/46.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 46.48/46.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 46.48/46.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 46.48/46.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 46.48/46.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 46.48/46.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 46.48/46.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 46.48/46.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 46.48/46.73  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 46.48/46.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 46.48/46.73  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 46.48/46.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 46.48/46.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 46.48/46.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 46.48/46.73  thf(t28_funct_2, conjecture,
% 46.48/46.73    (![A:$i,B:$i,C:$i,D:$i]:
% 46.48/46.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 46.48/46.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 46.48/46.73       ( ![E:$i]:
% 46.48/46.73         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 46.48/46.73             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 46.48/46.73           ( ( ( ( k2_relset_1 @
% 46.48/46.73                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 46.48/46.73                 ( C ) ) & 
% 46.48/46.73               ( v2_funct_1 @ E ) ) =>
% 46.48/46.73             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 46.48/46.73               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 46.48/46.73  thf(zf_stmt_0, negated_conjecture,
% 46.48/46.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 46.48/46.73        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 46.48/46.73            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 46.48/46.73          ( ![E:$i]:
% 46.48/46.73            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 46.48/46.73                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 46.48/46.73              ( ( ( ( k2_relset_1 @
% 46.48/46.73                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 46.48/46.73                    ( C ) ) & 
% 46.48/46.73                  ( v2_funct_1 @ E ) ) =>
% 46.48/46.73                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 46.48/46.73                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 46.48/46.73    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 46.48/46.73  thf('0', plain,
% 46.48/46.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 46.48/46.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.73  thf(cc2_relset_1, axiom,
% 46.48/46.73    (![A:$i,B:$i,C:$i]:
% 46.48/46.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.48/46.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 46.48/46.73  thf('1', plain,
% 46.48/46.73      (![X22 : $i, X23 : $i, X24 : $i]:
% 46.48/46.73         ((v5_relat_1 @ X22 @ X24)
% 46.48/46.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 46.48/46.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 46.48/46.73  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 46.48/46.73      inference('sup-', [status(thm)], ['0', '1'])).
% 46.48/46.73  thf(d19_relat_1, axiom,
% 46.48/46.73    (![A:$i,B:$i]:
% 46.48/46.73     ( ( v1_relat_1 @ B ) =>
% 46.48/46.73       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 46.48/46.73  thf('3', plain,
% 46.48/46.73      (![X3 : $i, X4 : $i]:
% 46.48/46.73         (~ (v5_relat_1 @ X3 @ X4)
% 46.48/46.73          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 46.48/46.73          | ~ (v1_relat_1 @ X3))),
% 46.48/46.73      inference('cnf', [status(esa)], [d19_relat_1])).
% 46.48/46.73  thf('4', plain,
% 46.48/46.73      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 46.48/46.73      inference('sup-', [status(thm)], ['2', '3'])).
% 46.48/46.73  thf('5', plain,
% 46.48/46.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 46.48/46.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.73  thf(cc1_relset_1, axiom,
% 46.48/46.73    (![A:$i,B:$i,C:$i]:
% 46.48/46.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.48/46.73       ( v1_relat_1 @ C ) ))).
% 46.48/46.73  thf('6', plain,
% 46.48/46.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 46.48/46.73         ((v1_relat_1 @ X19)
% 46.48/46.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 46.48/46.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 46.48/46.73  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 46.48/46.73      inference('sup-', [status(thm)], ['5', '6'])).
% 46.48/46.73  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 46.48/46.73      inference('demod', [status(thm)], ['4', '7'])).
% 46.48/46.73  thf(d10_xboole_0, axiom,
% 46.48/46.73    (![A:$i,B:$i]:
% 46.48/46.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 46.48/46.73  thf('9', plain,
% 46.48/46.73      (![X0 : $i, X2 : $i]:
% 46.48/46.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 46.48/46.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 46.48/46.73  thf('10', plain,
% 46.48/46.73      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 46.48/46.73        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 46.48/46.73      inference('sup-', [status(thm)], ['8', '9'])).
% 46.48/46.73  thf('11', plain,
% 46.48/46.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 46.48/46.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.73  thf('12', plain,
% 46.48/46.73      (![X22 : $i, X23 : $i, X24 : $i]:
% 46.48/46.73         ((v4_relat_1 @ X22 @ X23)
% 46.48/46.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 46.48/46.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 46.48/46.73  thf('13', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 46.48/46.73      inference('sup-', [status(thm)], ['11', '12'])).
% 46.48/46.73  thf(t209_relat_1, axiom,
% 46.48/46.73    (![A:$i,B:$i]:
% 46.48/46.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 46.48/46.73       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 46.48/46.73  thf('14', plain,
% 46.48/46.73      (![X15 : $i, X16 : $i]:
% 46.48/46.73         (((X15) = (k7_relat_1 @ X15 @ X16))
% 46.48/46.73          | ~ (v4_relat_1 @ X15 @ X16)
% 46.48/46.73          | ~ (v1_relat_1 @ X15))),
% 46.48/46.73      inference('cnf', [status(esa)], [t209_relat_1])).
% 46.48/46.73  thf('15', plain,
% 46.48/46.74      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['13', '14'])).
% 46.48/46.74  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 46.48/46.74      inference('sup-', [status(thm)], ['5', '6'])).
% 46.48/46.74  thf('17', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 46.48/46.74      inference('demod', [status(thm)], ['15', '16'])).
% 46.48/46.74  thf(t148_relat_1, axiom,
% 46.48/46.74    (![A:$i,B:$i]:
% 46.48/46.74     ( ( v1_relat_1 @ B ) =>
% 46.48/46.74       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 46.48/46.74  thf('18', plain,
% 46.48/46.74      (![X11 : $i, X12 : $i]:
% 46.48/46.74         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 46.48/46.74          | ~ (v1_relat_1 @ X11))),
% 46.48/46.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.48/46.74  thf(t160_relat_1, axiom,
% 46.48/46.74    (![A:$i]:
% 46.48/46.74     ( ( v1_relat_1 @ A ) =>
% 46.48/46.74       ( ![B:$i]:
% 46.48/46.74         ( ( v1_relat_1 @ B ) =>
% 46.48/46.74           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 46.48/46.74             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 46.48/46.74  thf('19', plain,
% 46.48/46.74      (![X13 : $i, X14 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X13)
% 46.48/46.74          | ((k2_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 46.48/46.74              = (k9_relat_1 @ X13 @ (k2_relat_1 @ X14)))
% 46.48/46.74          | ~ (v1_relat_1 @ X14))),
% 46.48/46.74      inference('cnf', [status(esa)], [t160_relat_1])).
% 46.48/46.74  thf('20', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.48/46.74         (((k2_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 46.48/46.74            = (k9_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 46.48/46.74          | ~ (v1_relat_1 @ X2))),
% 46.48/46.74      inference('sup+', [status(thm)], ['18', '19'])).
% 46.48/46.74  thf('21', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ sk_D)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ sk_D)
% 46.48/46.74          | ((k2_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_D @ sk_A) @ X0))
% 46.48/46.74              = (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_D @ sk_A))))),
% 46.48/46.74      inference('sup-', [status(thm)], ['17', '20'])).
% 46.48/46.74  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 46.48/46.74      inference('sup-', [status(thm)], ['5', '6'])).
% 46.48/46.74  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 46.48/46.74      inference('sup-', [status(thm)], ['5', '6'])).
% 46.48/46.74  thf('24', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 46.48/46.74      inference('demod', [status(thm)], ['15', '16'])).
% 46.48/46.74  thf('25', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 46.48/46.74      inference('demod', [status(thm)], ['15', '16'])).
% 46.48/46.74  thf('26', plain,
% 46.48/46.74      (![X11 : $i, X12 : $i]:
% 46.48/46.74         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 46.48/46.74          | ~ (v1_relat_1 @ X11))),
% 46.48/46.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.48/46.74  thf('27', plain,
% 46.48/46.74      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))
% 46.48/46.74        | ~ (v1_relat_1 @ sk_D))),
% 46.48/46.74      inference('sup+', [status(thm)], ['25', '26'])).
% 46.48/46.74  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 46.48/46.74      inference('sup-', [status(thm)], ['5', '6'])).
% 46.48/46.74  thf('29', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))),
% 46.48/46.74      inference('demod', [status(thm)], ['27', '28'])).
% 46.48/46.74  thf('30', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0))
% 46.48/46.74              = (k9_relat_1 @ X0 @ (k2_relat_1 @ sk_D))))),
% 46.48/46.74      inference('demod', [status(thm)], ['21', '22', '23', '24', '29'])).
% 46.48/46.74  thf('31', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf(d1_funct_2, axiom,
% 46.48/46.74    (![A:$i,B:$i,C:$i]:
% 46.48/46.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.48/46.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 46.48/46.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 46.48/46.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 46.48/46.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 46.48/46.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 46.48/46.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 46.48/46.74  thf(zf_stmt_1, axiom,
% 46.48/46.74    (![C:$i,B:$i,A:$i]:
% 46.48/46.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 46.48/46.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 46.48/46.74  thf('32', plain,
% 46.48/46.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 46.48/46.74         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 46.48/46.74          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 46.48/46.74          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 46.48/46.74  thf('33', plain,
% 46.48/46.74      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 46.48/46.74        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['31', '32'])).
% 46.48/46.74  thf(zf_stmt_2, axiom,
% 46.48/46.74    (![B:$i,A:$i]:
% 46.48/46.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 46.48/46.74       ( zip_tseitin_0 @ B @ A ) ))).
% 46.48/46.74  thf('34', plain,
% 46.48/46.74      (![X31 : $i, X32 : $i]:
% 46.48/46.74         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 46.48/46.74  thf('35', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 46.48/46.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 46.48/46.74  thf(zf_stmt_5, axiom,
% 46.48/46.74    (![A:$i,B:$i,C:$i]:
% 46.48/46.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.48/46.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 46.48/46.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 46.48/46.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 46.48/46.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 46.48/46.74  thf('36', plain,
% 46.48/46.74      (![X36 : $i, X37 : $i, X38 : $i]:
% 46.48/46.74         (~ (zip_tseitin_0 @ X36 @ X37)
% 46.48/46.74          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 46.48/46.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 46.48/46.74  thf('37', plain,
% 46.48/46.74      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 46.48/46.74      inference('sup-', [status(thm)], ['35', '36'])).
% 46.48/46.74  thf('38', plain,
% 46.48/46.74      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 46.48/46.74      inference('sup-', [status(thm)], ['34', '37'])).
% 46.48/46.74  thf('39', plain, (((sk_C) != (k1_xboole_0))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('40', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 46.48/46.74      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 46.48/46.74  thf('41', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf(redefinition_k1_relset_1, axiom,
% 46.48/46.74    (![A:$i,B:$i,C:$i]:
% 46.48/46.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.48/46.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 46.48/46.74  thf('42', plain,
% 46.48/46.74      (![X25 : $i, X26 : $i, X27 : $i]:
% 46.48/46.74         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 46.48/46.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 46.48/46.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 46.48/46.74  thf('43', plain,
% 46.48/46.74      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 46.48/46.74      inference('sup-', [status(thm)], ['41', '42'])).
% 46.48/46.74  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['33', '40', '43'])).
% 46.48/46.74  thf(t147_relat_1, axiom,
% 46.48/46.74    (![A:$i,B:$i]:
% 46.48/46.74     ( ( v1_relat_1 @ B ) =>
% 46.48/46.74       ( r1_tarski @
% 46.48/46.74         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 46.48/46.74  thf('45', plain,
% 46.48/46.74      (![X9 : $i, X10 : $i]:
% 46.48/46.74         ((r1_tarski @ (k9_relat_1 @ X9 @ X10) @ 
% 46.48/46.74           (k9_relat_1 @ X9 @ (k1_relat_1 @ X9)))
% 46.48/46.74          | ~ (v1_relat_1 @ X9))),
% 46.48/46.74      inference('cnf', [status(esa)], [t147_relat_1])).
% 46.48/46.74  thf('46', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         ((r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ (k9_relat_1 @ sk_E @ sk_B))
% 46.48/46.74          | ~ (v1_relat_1 @ sk_E))),
% 46.48/46.74      inference('sup+', [status(thm)], ['44', '45'])).
% 46.48/46.74  thf('47', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('48', plain,
% 46.48/46.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 46.48/46.74         ((v4_relat_1 @ X22 @ X23)
% 46.48/46.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 46.48/46.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 46.48/46.74  thf('49', plain, ((v4_relat_1 @ sk_E @ sk_B)),
% 46.48/46.74      inference('sup-', [status(thm)], ['47', '48'])).
% 46.48/46.74  thf('50', plain,
% 46.48/46.74      (![X15 : $i, X16 : $i]:
% 46.48/46.74         (((X15) = (k7_relat_1 @ X15 @ X16))
% 46.48/46.74          | ~ (v4_relat_1 @ X15 @ X16)
% 46.48/46.74          | ~ (v1_relat_1 @ X15))),
% 46.48/46.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 46.48/46.74  thf('51', plain,
% 46.48/46.74      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_B)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['49', '50'])).
% 46.48/46.74  thf('52', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('53', plain,
% 46.48/46.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 46.48/46.74         ((v1_relat_1 @ X19)
% 46.48/46.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 46.48/46.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 46.48/46.74  thf('54', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('55', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 46.48/46.74      inference('demod', [status(thm)], ['51', '54'])).
% 46.48/46.74  thf('56', plain,
% 46.48/46.74      (![X11 : $i, X12 : $i]:
% 46.48/46.74         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 46.48/46.74          | ~ (v1_relat_1 @ X11))),
% 46.48/46.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.48/46.74  thf('57', plain,
% 46.48/46.74      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 46.48/46.74        | ~ (v1_relat_1 @ sk_E))),
% 46.48/46.74      inference('sup+', [status(thm)], ['55', '56'])).
% 46.48/46.74  thf('58', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('59', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 46.48/46.74      inference('demod', [status(thm)], ['57', '58'])).
% 46.48/46.74  thf('60', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('61', plain,
% 46.48/46.74      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ (k2_relat_1 @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['46', '59', '60'])).
% 46.48/46.74  thf('62', plain,
% 46.48/46.74      (((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 46.48/46.74         (k2_relat_1 @ sk_E))
% 46.48/46.74        | ~ (v1_relat_1 @ sk_E))),
% 46.48/46.74      inference('sup+', [status(thm)], ['30', '61'])).
% 46.48/46.74  thf('63', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('64', plain,
% 46.48/46.74      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 46.48/46.74        (k2_relat_1 @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['62', '63'])).
% 46.48/46.74  thf('65', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 46.48/46.74      inference('demod', [status(thm)], ['57', '58'])).
% 46.48/46.74  thf('66', plain,
% 46.48/46.74      (![X11 : $i, X12 : $i]:
% 46.48/46.74         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 46.48/46.74          | ~ (v1_relat_1 @ X11))),
% 46.48/46.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.48/46.74  thf(t120_relat_1, axiom,
% 46.48/46.74    (![A:$i,B:$i]:
% 46.48/46.74     ( ( v1_relat_1 @ B ) =>
% 46.48/46.74       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 46.48/46.74         ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ))).
% 46.48/46.74  thf('67', plain,
% 46.48/46.74      (![X5 : $i, X6 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X5 @ (k2_relat_1 @ X6))
% 46.48/46.74          | ((k2_relat_1 @ (k8_relat_1 @ X5 @ X6)) = (X5))
% 46.48/46.74          | ~ (v1_relat_1 @ X6))),
% 46.48/46.74      inference('cnf', [status(esa)], [t120_relat_1])).
% 46.48/46.74  thf('68', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 46.48/46.74          | ((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) = (X2)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['66', '67'])).
% 46.48/46.74  thf('69', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_E))
% 46.48/46.74          | ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k7_relat_1 @ sk_E @ sk_B)))
% 46.48/46.74              = (X0))
% 46.48/46.74          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 46.48/46.74          | ~ (v1_relat_1 @ sk_E))),
% 46.48/46.74      inference('sup-', [status(thm)], ['65', '68'])).
% 46.48/46.74  thf('70', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 46.48/46.74      inference('demod', [status(thm)], ['51', '54'])).
% 46.48/46.74  thf('71', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 46.48/46.74      inference('demod', [status(thm)], ['51', '54'])).
% 46.48/46.74  thf('72', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('73', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('74', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_E))
% 46.48/46.74          | ((k2_relat_1 @ (k8_relat_1 @ X0 @ sk_E)) = (X0)))),
% 46.48/46.74      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 46.48/46.74  thf('75', plain,
% 46.48/46.74      (((k2_relat_1 @ 
% 46.48/46.74         (k8_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ sk_E))
% 46.48/46.74         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['64', '74'])).
% 46.48/46.74  thf('76', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0))
% 46.48/46.74              = (k9_relat_1 @ X0 @ (k2_relat_1 @ sk_D))))),
% 46.48/46.74      inference('demod', [status(thm)], ['21', '22', '23', '24', '29'])).
% 46.48/46.74  thf('77', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['33', '40', '43'])).
% 46.48/46.74  thf('78', plain,
% 46.48/46.74      (![X9 : $i, X10 : $i]:
% 46.48/46.74         ((r1_tarski @ (k9_relat_1 @ X9 @ X10) @ 
% 46.48/46.74           (k9_relat_1 @ X9 @ (k1_relat_1 @ X9)))
% 46.48/46.74          | ~ (v1_relat_1 @ X9))),
% 46.48/46.74      inference('cnf', [status(esa)], [t147_relat_1])).
% 46.48/46.74  thf('79', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 46.48/46.74          | ((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))) = (X2)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['66', '67'])).
% 46.48/46.74  thf('80', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k8_relat_1 @ (k9_relat_1 @ X0 @ X1) @ 
% 46.48/46.74               (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 46.48/46.74              = (k9_relat_1 @ X0 @ X1))
% 46.48/46.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 46.48/46.74          | ~ (v1_relat_1 @ X0))),
% 46.48/46.74      inference('sup-', [status(thm)], ['78', '79'])).
% 46.48/46.74  thf('81', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k8_relat_1 @ (k9_relat_1 @ X0 @ X1) @ 
% 46.48/46.74               (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 46.48/46.74              = (k9_relat_1 @ X0 @ X1))
% 46.48/46.74          | ~ (v1_relat_1 @ X0))),
% 46.48/46.74      inference('simplify', [status(thm)], ['80'])).
% 46.48/46.74  thf('82', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 46.48/46.74          | ~ (v1_relat_1 @ sk_E)
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k8_relat_1 @ (k9_relat_1 @ sk_E @ X0) @ 
% 46.48/46.74               (k7_relat_1 @ sk_E @ (k1_relat_1 @ sk_E))))
% 46.48/46.74              = (k9_relat_1 @ sk_E @ X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['77', '81'])).
% 46.48/46.74  thf('83', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 46.48/46.74      inference('demod', [status(thm)], ['51', '54'])).
% 46.48/46.74  thf('84', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('85', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('86', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['33', '40', '43'])).
% 46.48/46.74  thf('87', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 46.48/46.74      inference('demod', [status(thm)], ['51', '54'])).
% 46.48/46.74  thf('88', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         ((k2_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_E @ X0) @ sk_E))
% 46.48/46.74           = (k9_relat_1 @ sk_E @ X0))),
% 46.48/46.74      inference('demod', [status(thm)], ['82', '83', '84', '85', '86', '87'])).
% 46.48/46.74  thf('89', plain,
% 46.48/46.74      ((((k2_relat_1 @ 
% 46.48/46.74          (k8_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ sk_E))
% 46.48/46.74          = (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 46.48/46.74        | ~ (v1_relat_1 @ sk_E))),
% 46.48/46.74      inference('sup+', [status(thm)], ['76', '88'])).
% 46.48/46.74  thf('90', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('91', plain,
% 46.48/46.74      (((k2_relat_1 @ 
% 46.48/46.74         (k8_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ sk_E))
% 46.48/46.74         = (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))),
% 46.48/46.74      inference('demod', [status(thm)], ['89', '90'])).
% 46.48/46.74  thf('92', plain,
% 46.48/46.74      (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))
% 46.48/46.74         = (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))),
% 46.48/46.74      inference('sup+', [status(thm)], ['75', '91'])).
% 46.48/46.74  thf('93', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('94', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf(dt_k1_partfun1, axiom,
% 46.48/46.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 46.48/46.74     ( ( ( v1_funct_1 @ E ) & 
% 46.48/46.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 46.48/46.74         ( v1_funct_1 @ F ) & 
% 46.48/46.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 46.48/46.74       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 46.48/46.74         ( m1_subset_1 @
% 46.48/46.74           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 46.48/46.74           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 46.48/46.74  thf('95', plain,
% 46.48/46.74      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 46.48/46.74         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 46.48/46.74          | ~ (v1_funct_1 @ X39)
% 46.48/46.74          | ~ (v1_funct_1 @ X42)
% 46.48/46.74          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 46.48/46.74          | (m1_subset_1 @ (k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42) @ 
% 46.48/46.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X44))))),
% 46.48/46.74      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 46.48/46.74  thf('96', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.48/46.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 46.48/46.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 46.48/46.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 46.48/46.74          | ~ (v1_funct_1 @ X1)
% 46.48/46.74          | ~ (v1_funct_1 @ sk_D))),
% 46.48/46.74      inference('sup-', [status(thm)], ['94', '95'])).
% 46.48/46.74  thf('97', plain, ((v1_funct_1 @ sk_D)),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('98', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.48/46.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 46.48/46.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 46.48/46.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 46.48/46.74          | ~ (v1_funct_1 @ X1))),
% 46.48/46.74      inference('demod', [status(thm)], ['96', '97'])).
% 46.48/46.74  thf('99', plain,
% 46.48/46.74      ((~ (v1_funct_1 @ sk_E)
% 46.48/46.74        | (m1_subset_1 @ 
% 46.48/46.74           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 46.48/46.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 46.48/46.74      inference('sup-', [status(thm)], ['93', '98'])).
% 46.48/46.74  thf('100', plain, ((v1_funct_1 @ sk_E)),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('101', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('102', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf(redefinition_k1_partfun1, axiom,
% 46.48/46.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 46.48/46.74     ( ( ( v1_funct_1 @ E ) & 
% 46.48/46.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 46.48/46.74         ( v1_funct_1 @ F ) & 
% 46.48/46.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 46.48/46.74       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 46.48/46.74  thf('103', plain,
% 46.48/46.74      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 46.48/46.74         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 46.48/46.74          | ~ (v1_funct_1 @ X45)
% 46.48/46.74          | ~ (v1_funct_1 @ X48)
% 46.48/46.74          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 46.48/46.74          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 46.48/46.74              = (k5_relat_1 @ X45 @ X48)))),
% 46.48/46.74      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 46.48/46.74  thf('104', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.48/46.74         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 46.48/46.74            = (k5_relat_1 @ sk_D @ X0))
% 46.48/46.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 46.48/46.74          | ~ (v1_funct_1 @ X0)
% 46.48/46.74          | ~ (v1_funct_1 @ sk_D))),
% 46.48/46.74      inference('sup-', [status(thm)], ['102', '103'])).
% 46.48/46.74  thf('105', plain, ((v1_funct_1 @ sk_D)),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('106', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.48/46.74         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 46.48/46.74            = (k5_relat_1 @ sk_D @ X0))
% 46.48/46.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 46.48/46.74          | ~ (v1_funct_1 @ X0))),
% 46.48/46.74      inference('demod', [status(thm)], ['104', '105'])).
% 46.48/46.74  thf('107', plain,
% 46.48/46.74      ((~ (v1_funct_1 @ sk_E)
% 46.48/46.74        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 46.48/46.74            = (k5_relat_1 @ sk_D @ sk_E)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['101', '106'])).
% 46.48/46.74  thf('108', plain, ((v1_funct_1 @ sk_E)),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('109', plain,
% 46.48/46.74      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 46.48/46.74         = (k5_relat_1 @ sk_D @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['107', '108'])).
% 46.48/46.74  thf('110', plain,
% 46.48/46.74      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 46.48/46.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 46.48/46.74      inference('demod', [status(thm)], ['99', '100', '109'])).
% 46.48/46.74  thf(redefinition_k2_relset_1, axiom,
% 46.48/46.74    (![A:$i,B:$i,C:$i]:
% 46.48/46.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.48/46.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 46.48/46.74  thf('111', plain,
% 46.48/46.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 46.48/46.74         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 46.48/46.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 46.48/46.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 46.48/46.74  thf('112', plain,
% 46.48/46.74      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 46.48/46.74         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['110', '111'])).
% 46.48/46.74  thf('113', plain,
% 46.48/46.74      (((k2_relset_1 @ sk_A @ sk_C @ 
% 46.48/46.74         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('114', plain,
% 46.48/46.74      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 46.48/46.74         = (k5_relat_1 @ sk_D @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['107', '108'])).
% 46.48/46.74  thf('115', plain,
% 46.48/46.74      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 46.48/46.74      inference('demod', [status(thm)], ['113', '114'])).
% 46.48/46.74  thf('116', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 46.48/46.74      inference('sup+', [status(thm)], ['112', '115'])).
% 46.48/46.74  thf('117', plain, (((sk_C) = (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))),
% 46.48/46.74      inference('demod', [status(thm)], ['92', '116'])).
% 46.48/46.74  thf('118', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 46.48/46.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 46.48/46.74  thf('119', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 46.48/46.74      inference('simplify', [status(thm)], ['118'])).
% 46.48/46.74  thf(t125_relat_1, axiom,
% 46.48/46.74    (![A:$i,B:$i]:
% 46.48/46.74     ( ( v1_relat_1 @ B ) =>
% 46.48/46.74       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 46.48/46.74         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 46.48/46.74  thf('120', plain,
% 46.48/46.74      (![X7 : $i, X8 : $i]:
% 46.48/46.74         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 46.48/46.74          | ((k8_relat_1 @ X8 @ X7) = (X7))
% 46.48/46.74          | ~ (v1_relat_1 @ X7))),
% 46.48/46.74      inference('cnf', [status(esa)], [t125_relat_1])).
% 46.48/46.74  thf('121', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['119', '120'])).
% 46.48/46.74  thf('122', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['119', '120'])).
% 46.48/46.74  thf('123', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['119', '120'])).
% 46.48/46.74  thf('124', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['119', '120'])).
% 46.48/46.74  thf('125', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['119', '120'])).
% 46.48/46.74  thf('126', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 46.48/46.74      inference('simplify', [status(thm)], ['118'])).
% 46.48/46.74  thf('127', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['119', '120'])).
% 46.48/46.74  thf('128', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 46.48/46.74      inference('simplify', [status(thm)], ['118'])).
% 46.48/46.74  thf('129', plain,
% 46.48/46.74      (![X5 : $i, X6 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X5 @ (k2_relat_1 @ X6))
% 46.48/46.74          | ((k2_relat_1 @ (k8_relat_1 @ X5 @ X6)) = (X5))
% 46.48/46.74          | ~ (v1_relat_1 @ X6))),
% 46.48/46.74      inference('cnf', [status(esa)], [t120_relat_1])).
% 46.48/46.74  thf('130', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 46.48/46.74              = (k2_relat_1 @ X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['128', '129'])).
% 46.48/46.74  thf('131', plain,
% 46.48/46.74      (![X5 : $i, X6 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X5 @ (k2_relat_1 @ X6))
% 46.48/46.74          | ((k2_relat_1 @ (k8_relat_1 @ X5 @ X6)) = (X5))
% 46.48/46.74          | ~ (v1_relat_1 @ X6))),
% 46.48/46.74      inference('cnf', [status(esa)], [t120_relat_1])).
% 46.48/46.74  thf('132', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k8_relat_1 @ X1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))) = (
% 46.48/46.74              X1)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['130', '131'])).
% 46.48/46.74  thf('133', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k8_relat_1 @ X1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))) = (
% 46.48/46.74              X1))
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (r1_tarski @ X1 @ (k2_relat_1 @ X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['127', '132'])).
% 46.48/46.74  thf('134', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k8_relat_1 @ X1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))) = (
% 46.48/46.74              X1))
% 46.48/46.74          | ~ (v1_relat_1 @ X0))),
% 46.48/46.74      inference('simplify', [status(thm)], ['133'])).
% 46.48/46.74  thf('135', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 46.48/46.74               (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 46.48/46.74              = (k2_relat_1 @ X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['126', '134'])).
% 46.48/46.74  thf('136', plain,
% 46.48/46.74      (![X13 : $i, X14 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X13)
% 46.48/46.74          | ((k2_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 46.48/46.74              = (k9_relat_1 @ X13 @ (k2_relat_1 @ X14)))
% 46.48/46.74          | ~ (v1_relat_1 @ X14))),
% 46.48/46.74      inference('cnf', [status(esa)], [t160_relat_1])).
% 46.48/46.74  thf('137', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (((k2_relat_1 @ 
% 46.48/46.74            (k5_relat_1 @ 
% 46.48/46.74             (k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 46.48/46.74              (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)) @ 
% 46.48/46.74             X1))
% 46.48/46.74            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ 
% 46.48/46.74               (k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 46.48/46.74                (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 46.48/46.74          | ~ (v1_relat_1 @ X1))),
% 46.48/46.74      inference('sup+', [status(thm)], ['135', '136'])).
% 46.48/46.74  thf('138', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k5_relat_1 @ 
% 46.48/46.74               (k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 46.48/46.74                (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)) @ 
% 46.48/46.74               X1))
% 46.48/46.74              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 46.48/46.74      inference('sup-', [status(thm)], ['125', '137'])).
% 46.48/46.74  thf('139', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (((k2_relat_1 @ 
% 46.48/46.74            (k5_relat_1 @ 
% 46.48/46.74             (k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 46.48/46.74              (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)) @ 
% 46.48/46.74             X1))
% 46.48/46.74            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))),
% 46.48/46.74      inference('simplify', [status(thm)], ['138'])).
% 46.48/46.74  thf('140', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k5_relat_1 @ 
% 46.48/46.74               (k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 46.48/46.74                (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)) @ 
% 46.48/46.74               X1))
% 46.48/46.74              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 46.48/46.74      inference('sup-', [status(thm)], ['124', '139'])).
% 46.48/46.74  thf('141', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (((k2_relat_1 @ 
% 46.48/46.74            (k5_relat_1 @ 
% 46.48/46.74             (k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 46.48/46.74              (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)) @ 
% 46.48/46.74             X1))
% 46.48/46.74            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X0))),
% 46.48/46.74      inference('simplify', [status(thm)], ['140'])).
% 46.48/46.74  thf('142', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (((k2_relat_1 @ 
% 46.48/46.74            (k5_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0) @ X1))
% 46.48/46.74            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X1))),
% 46.48/46.74      inference('sup+', [status(thm)], ['123', '141'])).
% 46.48/46.74  thf('143', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k2_relat_1 @ 
% 46.48/46.74              (k5_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0) @ X1))
% 46.48/46.74              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 46.48/46.74      inference('simplify', [status(thm)], ['142'])).
% 46.48/46.74  thf(t51_funct_1, axiom,
% 46.48/46.74    (![A:$i]:
% 46.48/46.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 46.48/46.74       ( ![B:$i]:
% 46.48/46.74         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 46.48/46.74           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 46.48/46.74               ( v2_funct_1 @ A ) ) =>
% 46.48/46.74             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 46.48/46.74  thf('144', plain,
% 46.48/46.74      (![X17 : $i, X18 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X17)
% 46.48/46.74          | ~ (v1_funct_1 @ X17)
% 46.48/46.74          | (r1_tarski @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X17))
% 46.48/46.74          | ((k2_relat_1 @ (k5_relat_1 @ X17 @ X18)) != (k2_relat_1 @ X18))
% 46.48/46.74          | ~ (v2_funct_1 @ X18)
% 46.48/46.74          | ~ (v1_funct_1 @ X18)
% 46.48/46.74          | ~ (v1_relat_1 @ X18))),
% 46.48/46.74      inference('cnf', [status(esa)], [t51_funct_1])).
% 46.48/46.74  thf('145', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (((k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) != (k2_relat_1 @ X1))
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_funct_1 @ X1)
% 46.48/46.74          | ~ (v2_funct_1 @ X1)
% 46.48/46.74          | (r1_tarski @ (k1_relat_1 @ X1) @ 
% 46.48/46.74             (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 46.48/46.74          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 46.48/46.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['143', '144'])).
% 46.48/46.74  thf('146', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 46.48/46.74          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 46.48/46.74          | (r1_tarski @ (k1_relat_1 @ X1) @ 
% 46.48/46.74             (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 46.48/46.74          | ~ (v2_funct_1 @ X1)
% 46.48/46.74          | ~ (v1_funct_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) != (k2_relat_1 @ X1)))),
% 46.48/46.74      inference('simplify', [status(thm)], ['145'])).
% 46.48/46.74  thf('147', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) != (k2_relat_1 @ X1))
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_funct_1 @ X1)
% 46.48/46.74          | ~ (v2_funct_1 @ X1)
% 46.48/46.74          | (r1_tarski @ (k1_relat_1 @ X1) @ 
% 46.48/46.74             (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 46.48/46.74          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['122', '146'])).
% 46.48/46.74  thf('148', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 46.48/46.74          | (r1_tarski @ (k1_relat_1 @ X1) @ 
% 46.48/46.74             (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 46.48/46.74          | ~ (v2_funct_1 @ X1)
% 46.48/46.74          | ~ (v1_funct_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ((k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) != (k2_relat_1 @ X1))
% 46.48/46.74          | ~ (v1_relat_1 @ X0))),
% 46.48/46.74      inference('simplify', [status(thm)], ['147'])).
% 46.48/46.74  thf('149', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         (~ (v1_funct_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ((k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) != (k2_relat_1 @ X1))
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_funct_1 @ X1)
% 46.48/46.74          | ~ (v2_funct_1 @ X1)
% 46.48/46.74          | (r1_tarski @ (k1_relat_1 @ X1) @ 
% 46.48/46.74             (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))))),
% 46.48/46.74      inference('sup-', [status(thm)], ['121', '148'])).
% 46.48/46.74  thf('150', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i]:
% 46.48/46.74         ((r1_tarski @ (k1_relat_1 @ X1) @ 
% 46.48/46.74           (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 46.48/46.74          | ~ (v2_funct_1 @ X1)
% 46.48/46.74          | ~ (v1_funct_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ((k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) != (k2_relat_1 @ X1))
% 46.48/46.74          | ~ (v1_relat_1 @ X0)
% 46.48/46.74          | ~ (v1_funct_1 @ X0))),
% 46.48/46.74      inference('simplify', [status(thm)], ['149'])).
% 46.48/46.74  thf('151', plain,
% 46.48/46.74      ((((sk_C) != (k2_relat_1 @ sk_E))
% 46.48/46.74        | ~ (v1_funct_1 @ sk_D)
% 46.48/46.74        | ~ (v1_relat_1 @ sk_D)
% 46.48/46.74        | ~ (v1_relat_1 @ sk_E)
% 46.48/46.74        | ~ (v1_funct_1 @ sk_E)
% 46.48/46.74        | ~ (v2_funct_1 @ sk_E)
% 46.48/46.74        | (r1_tarski @ (k1_relat_1 @ sk_E) @ 
% 46.48/46.74           (k2_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_D) @ sk_D))))),
% 46.48/46.74      inference('sup-', [status(thm)], ['117', '150'])).
% 46.48/46.74  thf('152', plain,
% 46.48/46.74      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 46.48/46.74        (k2_relat_1 @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['62', '63'])).
% 46.48/46.74  thf('153', plain,
% 46.48/46.74      (![X0 : $i, X2 : $i]:
% 46.48/46.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 46.48/46.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 46.48/46.74  thf('154', plain,
% 46.48/46.74      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ 
% 46.48/46.74           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 46.48/46.74        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))))),
% 46.48/46.74      inference('sup-', [status(thm)], ['152', '153'])).
% 46.48/46.74  thf('155', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 46.48/46.74      inference('sup+', [status(thm)], ['112', '115'])).
% 46.48/46.74  thf('156', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('157', plain,
% 46.48/46.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 46.48/46.74         ((v5_relat_1 @ X22 @ X24)
% 46.48/46.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 46.48/46.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 46.48/46.74  thf('158', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 46.48/46.74      inference('sup-', [status(thm)], ['156', '157'])).
% 46.48/46.74  thf('159', plain,
% 46.48/46.74      (![X3 : $i, X4 : $i]:
% 46.48/46.74         (~ (v5_relat_1 @ X3 @ X4)
% 46.48/46.74          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 46.48/46.74          | ~ (v1_relat_1 @ X3))),
% 46.48/46.74      inference('cnf', [status(esa)], [d19_relat_1])).
% 46.48/46.74  thf('160', plain,
% 46.48/46.74      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 46.48/46.74      inference('sup-', [status(thm)], ['158', '159'])).
% 46.48/46.74  thf('161', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('162', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 46.48/46.74      inference('demod', [status(thm)], ['160', '161'])).
% 46.48/46.74  thf('163', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 46.48/46.74      inference('sup+', [status(thm)], ['112', '115'])).
% 46.48/46.74  thf('164', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 46.48/46.74      inference('demod', [status(thm)], ['154', '155', '162', '163'])).
% 46.48/46.74  thf('165', plain, ((v1_funct_1 @ sk_D)),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('166', plain, ((v1_relat_1 @ sk_D)),
% 46.48/46.74      inference('sup-', [status(thm)], ['5', '6'])).
% 46.48/46.74  thf('167', plain, ((v1_relat_1 @ sk_E)),
% 46.48/46.74      inference('sup-', [status(thm)], ['52', '53'])).
% 46.48/46.74  thf('168', plain, ((v1_funct_1 @ sk_E)),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('169', plain, ((v2_funct_1 @ sk_E)),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('170', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 46.48/46.74      inference('demod', [status(thm)], ['33', '40', '43'])).
% 46.48/46.74  thf('171', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 46.48/46.74      inference('simplify', [status(thm)], ['118'])).
% 46.48/46.74  thf('172', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))),
% 46.48/46.74      inference('demod', [status(thm)], ['27', '28'])).
% 46.48/46.74  thf('173', plain,
% 46.48/46.74      (![X11 : $i, X12 : $i]:
% 46.48/46.74         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 46.48/46.74          | ~ (v1_relat_1 @ X11))),
% 46.48/46.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 46.48/46.74  thf('174', plain,
% 46.48/46.74      (![X7 : $i, X8 : $i]:
% 46.48/46.74         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 46.48/46.74          | ((k8_relat_1 @ X8 @ X7) = (X7))
% 46.48/46.74          | ~ (v1_relat_1 @ X7))),
% 46.48/46.74      inference('cnf', [status(esa)], [t125_relat_1])).
% 46.48/46.74  thf('175', plain,
% 46.48/46.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.48/46.74         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 46.48/46.74          | ~ (v1_relat_1 @ X1)
% 46.48/46.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 46.48/46.74          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 46.48/46.74              = (k7_relat_1 @ X1 @ X0)))),
% 46.48/46.74      inference('sup-', [status(thm)], ['173', '174'])).
% 46.48/46.74  thf('176', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 46.48/46.74          | ((k8_relat_1 @ X0 @ (k7_relat_1 @ sk_D @ sk_A))
% 46.48/46.74              = (k7_relat_1 @ sk_D @ sk_A))
% 46.48/46.74          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ sk_A))
% 46.48/46.74          | ~ (v1_relat_1 @ sk_D))),
% 46.48/46.74      inference('sup-', [status(thm)], ['172', '175'])).
% 46.48/46.74  thf('177', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 46.48/46.74      inference('demod', [status(thm)], ['15', '16'])).
% 46.48/46.74  thf('178', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 46.48/46.74      inference('demod', [status(thm)], ['15', '16'])).
% 46.48/46.74  thf('179', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 46.48/46.74      inference('demod', [status(thm)], ['15', '16'])).
% 46.48/46.74  thf('180', plain, ((v1_relat_1 @ sk_D)),
% 46.48/46.74      inference('sup-', [status(thm)], ['5', '6'])).
% 46.48/46.74  thf('181', plain, ((v1_relat_1 @ sk_D)),
% 46.48/46.74      inference('sup-', [status(thm)], ['5', '6'])).
% 46.48/46.74  thf('182', plain,
% 46.48/46.74      (![X0 : $i]:
% 46.48/46.74         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 46.48/46.74          | ((k8_relat_1 @ X0 @ sk_D) = (sk_D)))),
% 46.48/46.74      inference('demod', [status(thm)],
% 46.48/46.74                ['176', '177', '178', '179', '180', '181'])).
% 46.48/46.74  thf('183', plain, (((k8_relat_1 @ (k2_relat_1 @ sk_D) @ sk_D) = (sk_D))),
% 46.48/46.74      inference('sup-', [status(thm)], ['171', '182'])).
% 46.48/46.74  thf('184', plain,
% 46.48/46.74      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 46.48/46.74      inference('demod', [status(thm)],
% 46.48/46.74                ['151', '164', '165', '166', '167', '168', '169', '170', '183'])).
% 46.48/46.74  thf('185', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 46.48/46.74      inference('simplify', [status(thm)], ['184'])).
% 46.48/46.74  thf('186', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 46.48/46.74      inference('demod', [status(thm)], ['10', '185'])).
% 46.48/46.74  thf('187', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('188', plain,
% 46.48/46.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 46.48/46.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.48/46.74  thf('189', plain,
% 46.48/46.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 46.48/46.74         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 46.48/46.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 46.48/46.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 46.48/46.74  thf('190', plain,
% 46.48/46.74      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 46.48/46.74      inference('sup-', [status(thm)], ['188', '189'])).
% 46.48/46.74  thf('191', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 46.48/46.74      inference('demod', [status(thm)], ['187', '190'])).
% 46.48/46.74  thf('192', plain, ($false),
% 46.48/46.74      inference('simplify_reflect-', [status(thm)], ['186', '191'])).
% 46.48/46.74  
% 46.48/46.74  % SZS output end Refutation
% 46.48/46.74  
% 46.60/46.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
