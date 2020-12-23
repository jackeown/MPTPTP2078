%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eGePhBbeHI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:58 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 378 expanded)
%              Number of leaves         :   52 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          : 1340 (6802 expanded)
%              Number of equality atoms :   91 ( 429 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_2 @ X49 @ X47 @ X48 )
      | ( X47
        = ( k1_relset_1 @ X47 @ X48 @ X49 ) )
      | ~ ( zip_tseitin_1 @ X49 @ X48 @ X47 ) ) ),
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
    ! [X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 )
      | ( X45 = k1_xboole_0 ) ) ),
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
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( zip_tseitin_0 @ X50 @ X51 )
      | ( zip_tseitin_1 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('34',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_E ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_E ) @ sk_C )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k10_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ X12 @ ( k3_xboole_0 @ ( k2_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_E @ sk_B ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('49',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('50',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('51',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_E ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52'])).

thf('54',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k10_relat_1 @ sk_E @ ( k2_relat_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['42','53'])).

thf('55',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('56',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('59',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['18','31','54','55','56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('62',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k9_relat_1 @ X10 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('80',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('85',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k4_relset_1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
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

thf('94',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ( ( k1_partfun1 @ X54 @ X55 @ X57 @ X58 @ X53 @ X56 )
        = ( k5_relat_1 @ X53 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['91','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['90','101'])).

thf('103',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['77','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['24','25'])).

thf('108',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['103','106','107'])).

thf('109',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','108'])).

thf('110',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['59','109'])).

thf('111',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('113',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['110','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eGePhBbeHI
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.54/2.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.54/2.73  % Solved by: fo/fo7.sh
% 2.54/2.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.54/2.73  % done 1226 iterations in 2.275s
% 2.54/2.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.54/2.73  % SZS output start Refutation
% 2.54/2.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.54/2.73  thf(sk_C_type, type, sk_C: $i).
% 2.54/2.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.54/2.73  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.54/2.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.54/2.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.54/2.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.54/2.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.54/2.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.54/2.73  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.54/2.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.54/2.73  thf(sk_B_type, type, sk_B: $i).
% 2.54/2.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.54/2.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.54/2.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.54/2.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.54/2.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.54/2.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.54/2.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.54/2.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.54/2.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.54/2.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.54/2.73  thf(sk_A_type, type, sk_A: $i).
% 2.54/2.73  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.54/2.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.54/2.73  thf(sk_D_type, type, sk_D: $i).
% 2.54/2.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.54/2.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.54/2.73  thf(sk_E_type, type, sk_E: $i).
% 2.54/2.73  thf(t28_funct_2, conjecture,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i]:
% 2.54/2.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.54/2.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.54/2.73       ( ![E:$i]:
% 2.54/2.73         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.54/2.73             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.54/2.73           ( ( ( ( k2_relset_1 @
% 2.54/2.73                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.54/2.73                 ( C ) ) & 
% 2.54/2.73               ( v2_funct_1 @ E ) ) =>
% 2.54/2.73             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.54/2.73               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 2.54/2.73  thf(zf_stmt_0, negated_conjecture,
% 2.54/2.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.54/2.73        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.54/2.73            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.54/2.73          ( ![E:$i]:
% 2.54/2.73            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.54/2.73                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.54/2.73              ( ( ( ( k2_relset_1 @
% 2.54/2.73                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.54/2.73                    ( C ) ) & 
% 2.54/2.73                  ( v2_funct_1 @ E ) ) =>
% 2.54/2.73                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.54/2.73                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 2.54/2.73    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 2.54/2.73  thf('0', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(d1_funct_2, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.54/2.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.54/2.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.54/2.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.54/2.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.54/2.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.54/2.73  thf(zf_stmt_1, axiom,
% 2.54/2.73    (![C:$i,B:$i,A:$i]:
% 2.54/2.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.54/2.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.54/2.73  thf('1', plain,
% 2.54/2.73      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.54/2.73         (~ (v1_funct_2 @ X49 @ X47 @ X48)
% 2.54/2.73          | ((X47) = (k1_relset_1 @ X47 @ X48 @ X49))
% 2.54/2.73          | ~ (zip_tseitin_1 @ X49 @ X48 @ X47))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.54/2.73  thf('2', plain,
% 2.54/2.73      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.54/2.73        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['0', '1'])).
% 2.54/2.73  thf(zf_stmt_2, axiom,
% 2.54/2.73    (![B:$i,A:$i]:
% 2.54/2.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.54/2.73       ( zip_tseitin_0 @ B @ A ) ))).
% 2.54/2.73  thf('3', plain,
% 2.54/2.73      (![X45 : $i, X46 : $i]:
% 2.54/2.73         ((zip_tseitin_0 @ X45 @ X46) | ((X45) = (k1_xboole_0)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.54/2.73  thf('4', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.54/2.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.54/2.73  thf(zf_stmt_5, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.54/2.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.54/2.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.54/2.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.54/2.73  thf('5', plain,
% 2.54/2.73      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.54/2.73         (~ (zip_tseitin_0 @ X50 @ X51)
% 2.54/2.73          | (zip_tseitin_1 @ X52 @ X50 @ X51)
% 2.54/2.73          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50))))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.54/2.73  thf('6', plain,
% 2.54/2.73      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.54/2.73      inference('sup-', [status(thm)], ['4', '5'])).
% 2.54/2.73  thf('7', plain,
% 2.54/2.73      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.54/2.73      inference('sup-', [status(thm)], ['3', '6'])).
% 2.54/2.73  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('9', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.54/2.73      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 2.54/2.73  thf('10', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(redefinition_k1_relset_1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.54/2.73  thf('11', plain,
% 2.54/2.73      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.54/2.73         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 2.54/2.73          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 2.54/2.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.54/2.73  thf('12', plain,
% 2.54/2.73      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.54/2.73      inference('sup-', [status(thm)], ['10', '11'])).
% 2.54/2.73  thf('13', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.54/2.73      inference('demod', [status(thm)], ['2', '9', '12'])).
% 2.54/2.73  thf(d10_xboole_0, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.54/2.73  thf('14', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.54/2.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.54/2.73  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.54/2.73      inference('simplify', [status(thm)], ['14'])).
% 2.54/2.73  thf(t164_funct_1, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.54/2.73       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 2.54/2.73         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.54/2.73  thf('16', plain,
% 2.54/2.73      (![X16 : $i, X17 : $i]:
% 2.54/2.73         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 2.54/2.73          | ~ (v2_funct_1 @ X17)
% 2.54/2.73          | ((k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X16)) = (X16))
% 2.54/2.73          | ~ (v1_funct_1 @ X17)
% 2.54/2.73          | ~ (v1_relat_1 @ X17))),
% 2.54/2.73      inference('cnf', [status(esa)], [t164_funct_1])).
% 2.54/2.73  thf('17', plain,
% 2.54/2.73      (![X0 : $i]:
% 2.54/2.73         (~ (v1_relat_1 @ X0)
% 2.54/2.73          | ~ (v1_funct_1 @ X0)
% 2.54/2.73          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.54/2.73              = (k1_relat_1 @ X0))
% 2.54/2.73          | ~ (v2_funct_1 @ X0))),
% 2.54/2.73      inference('sup-', [status(thm)], ['15', '16'])).
% 2.54/2.73  thf('18', plain,
% 2.54/2.73      ((((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ sk_B))
% 2.54/2.73          = (k1_relat_1 @ sk_E))
% 2.54/2.73        | ~ (v2_funct_1 @ sk_E)
% 2.54/2.73        | ~ (v1_funct_1 @ sk_E)
% 2.54/2.73        | ~ (v1_relat_1 @ sk_E))),
% 2.54/2.73      inference('sup+', [status(thm)], ['13', '17'])).
% 2.54/2.73  thf('19', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(cc2_relset_1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.54/2.73  thf('20', plain,
% 2.54/2.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.54/2.73         ((v4_relat_1 @ X21 @ X22)
% 2.54/2.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.54/2.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.54/2.73  thf('21', plain, ((v4_relat_1 @ sk_E @ sk_B)),
% 2.54/2.73      inference('sup-', [status(thm)], ['19', '20'])).
% 2.54/2.73  thf(t209_relat_1, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.54/2.73       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.54/2.73  thf('22', plain,
% 2.54/2.73      (![X14 : $i, X15 : $i]:
% 2.54/2.73         (((X14) = (k7_relat_1 @ X14 @ X15))
% 2.54/2.73          | ~ (v4_relat_1 @ X14 @ X15)
% 2.54/2.73          | ~ (v1_relat_1 @ X14))),
% 2.54/2.73      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.54/2.73  thf('23', plain,
% 2.54/2.73      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_B)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['21', '22'])).
% 2.54/2.73  thf('24', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(cc1_relset_1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.73       ( v1_relat_1 @ C ) ))).
% 2.54/2.73  thf('25', plain,
% 2.54/2.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.54/2.73         ((v1_relat_1 @ X18)
% 2.54/2.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.54/2.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.54/2.73  thf('26', plain, ((v1_relat_1 @ sk_E)),
% 2.54/2.73      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.73  thf('27', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 2.54/2.73      inference('demod', [status(thm)], ['23', '26'])).
% 2.54/2.73  thf(t148_relat_1, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( v1_relat_1 @ B ) =>
% 2.54/2.73       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.54/2.73  thf('28', plain,
% 2.54/2.73      (![X8 : $i, X9 : $i]:
% 2.54/2.73         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 2.54/2.73          | ~ (v1_relat_1 @ X8))),
% 2.54/2.73      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.54/2.73  thf('29', plain,
% 2.54/2.73      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 2.54/2.73        | ~ (v1_relat_1 @ sk_E))),
% 2.54/2.73      inference('sup+', [status(thm)], ['27', '28'])).
% 2.54/2.73  thf('30', plain, ((v1_relat_1 @ sk_E)),
% 2.54/2.73      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.73  thf('31', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 2.54/2.73      inference('demod', [status(thm)], ['29', '30'])).
% 2.54/2.73  thf('32', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(dt_k2_relset_1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.73       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.54/2.73  thf('33', plain,
% 2.54/2.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.54/2.73         ((m1_subset_1 @ (k2_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))
% 2.54/2.73          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.54/2.73      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 2.54/2.73  thf('34', plain,
% 2.54/2.73      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_E) @ (k1_zfmisc_1 @ sk_C))),
% 2.54/2.73      inference('sup-', [status(thm)], ['32', '33'])).
% 2.54/2.73  thf('35', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(redefinition_k2_relset_1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i]:
% 2.54/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.54/2.73  thf('36', plain,
% 2.54/2.73      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.54/2.73         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 2.54/2.73          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 2.54/2.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.54/2.73  thf('37', plain,
% 2.54/2.73      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 2.54/2.73      inference('sup-', [status(thm)], ['35', '36'])).
% 2.54/2.73  thf('38', plain,
% 2.54/2.73      ((m1_subset_1 @ (k2_relat_1 @ sk_E) @ (k1_zfmisc_1 @ sk_C))),
% 2.54/2.73      inference('demod', [status(thm)], ['34', '37'])).
% 2.54/2.73  thf(t3_subset, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.54/2.73  thf('39', plain,
% 2.54/2.73      (![X5 : $i, X6 : $i]:
% 2.54/2.73         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 2.54/2.73      inference('cnf', [status(esa)], [t3_subset])).
% 2.54/2.73  thf('40', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 2.54/2.73      inference('sup-', [status(thm)], ['38', '39'])).
% 2.54/2.73  thf(t28_xboole_1, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.54/2.73  thf('41', plain,
% 2.54/2.73      (![X3 : $i, X4 : $i]:
% 2.54/2.73         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 2.54/2.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.54/2.73  thf('42', plain,
% 2.54/2.73      (((k3_xboole_0 @ (k2_relat_1 @ sk_E) @ sk_C) = (k2_relat_1 @ sk_E))),
% 2.54/2.73      inference('sup-', [status(thm)], ['40', '41'])).
% 2.54/2.73  thf('43', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 2.54/2.73      inference('demod', [status(thm)], ['23', '26'])).
% 2.54/2.73  thf('44', plain,
% 2.54/2.73      (![X8 : $i, X9 : $i]:
% 2.54/2.73         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 2.54/2.73          | ~ (v1_relat_1 @ X8))),
% 2.54/2.73      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.54/2.73  thf(t168_relat_1, axiom,
% 2.54/2.73    (![A:$i,B:$i]:
% 2.54/2.73     ( ( v1_relat_1 @ B ) =>
% 2.54/2.73       ( ( k10_relat_1 @ B @ A ) =
% 2.54/2.73         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 2.54/2.73  thf('45', plain,
% 2.54/2.73      (![X12 : $i, X13 : $i]:
% 2.54/2.73         (((k10_relat_1 @ X12 @ X13)
% 2.54/2.73            = (k10_relat_1 @ X12 @ (k3_xboole_0 @ (k2_relat_1 @ X12) @ X13)))
% 2.54/2.73          | ~ (v1_relat_1 @ X12))),
% 2.54/2.73      inference('cnf', [status(esa)], [t168_relat_1])).
% 2.54/2.73  thf('46', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.73         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.54/2.73            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.54/2.73               (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)))
% 2.54/2.73          | ~ (v1_relat_1 @ X1)
% 2.54/2.73          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.54/2.73      inference('sup+', [status(thm)], ['44', '45'])).
% 2.54/2.73  thf('47', plain,
% 2.54/2.73      (![X0 : $i]:
% 2.54/2.73         (~ (v1_relat_1 @ sk_E)
% 2.54/2.73          | ~ (v1_relat_1 @ sk_E)
% 2.54/2.73          | ((k10_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ X0)
% 2.54/2.73              = (k10_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 2.54/2.73                 (k3_xboole_0 @ (k9_relat_1 @ sk_E @ sk_B) @ X0))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['43', '46'])).
% 2.54/2.73  thf('48', plain, ((v1_relat_1 @ sk_E)),
% 2.54/2.73      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.73  thf('49', plain, ((v1_relat_1 @ sk_E)),
% 2.54/2.73      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.73  thf('50', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 2.54/2.73      inference('demod', [status(thm)], ['23', '26'])).
% 2.54/2.73  thf('51', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 2.54/2.73      inference('demod', [status(thm)], ['23', '26'])).
% 2.54/2.73  thf('52', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 2.54/2.73      inference('demod', [status(thm)], ['29', '30'])).
% 2.54/2.73  thf('53', plain,
% 2.54/2.73      (![X0 : $i]:
% 2.54/2.73         ((k10_relat_1 @ sk_E @ X0)
% 2.54/2.73           = (k10_relat_1 @ sk_E @ (k3_xboole_0 @ (k2_relat_1 @ sk_E) @ X0)))),
% 2.54/2.73      inference('demod', [status(thm)], ['47', '48', '49', '50', '51', '52'])).
% 2.54/2.73  thf('54', plain,
% 2.54/2.73      (((k10_relat_1 @ sk_E @ sk_C)
% 2.54/2.73         = (k10_relat_1 @ sk_E @ (k2_relat_1 @ sk_E)))),
% 2.54/2.73      inference('sup+', [status(thm)], ['42', '53'])).
% 2.54/2.73  thf('55', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.54/2.73      inference('demod', [status(thm)], ['2', '9', '12'])).
% 2.54/2.73  thf('56', plain, ((v2_funct_1 @ sk_E)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('58', plain, ((v1_relat_1 @ sk_E)),
% 2.54/2.73      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.73  thf('59', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 2.54/2.73      inference('demod', [status(thm)],
% 2.54/2.73                ['18', '31', '54', '55', '56', '57', '58'])).
% 2.54/2.73  thf('60', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('61', plain,
% 2.54/2.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.54/2.73         ((m1_subset_1 @ (k2_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))
% 2.54/2.73          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.54/2.73      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 2.54/2.73  thf('62', plain,
% 2.54/2.73      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 2.54/2.73      inference('sup-', [status(thm)], ['60', '61'])).
% 2.54/2.73  thf('63', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('64', plain,
% 2.54/2.73      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.54/2.73         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 2.54/2.73          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 2.54/2.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.54/2.73  thf('65', plain,
% 2.54/2.73      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.54/2.73      inference('sup-', [status(thm)], ['63', '64'])).
% 2.54/2.73  thf('66', plain,
% 2.54/2.73      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 2.54/2.73      inference('demod', [status(thm)], ['62', '65'])).
% 2.54/2.73  thf('67', plain,
% 2.54/2.73      (![X5 : $i, X6 : $i]:
% 2.54/2.73         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 2.54/2.73      inference('cnf', [status(esa)], [t3_subset])).
% 2.54/2.73  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 2.54/2.73      inference('sup-', [status(thm)], ['66', '67'])).
% 2.54/2.73  thf('69', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.54/2.73      inference('demod', [status(thm)], ['2', '9', '12'])).
% 2.54/2.73  thf('70', plain,
% 2.54/2.73      (![X16 : $i, X17 : $i]:
% 2.54/2.73         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 2.54/2.73          | ~ (v2_funct_1 @ X17)
% 2.54/2.73          | ((k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X16)) = (X16))
% 2.54/2.73          | ~ (v1_funct_1 @ X17)
% 2.54/2.73          | ~ (v1_relat_1 @ X17))),
% 2.54/2.73      inference('cnf', [status(esa)], [t164_funct_1])).
% 2.54/2.73  thf('71', plain,
% 2.54/2.73      (![X0 : $i]:
% 2.54/2.73         (~ (r1_tarski @ X0 @ sk_B)
% 2.54/2.73          | ~ (v1_relat_1 @ sk_E)
% 2.54/2.73          | ~ (v1_funct_1 @ sk_E)
% 2.54/2.73          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0))
% 2.54/2.73          | ~ (v2_funct_1 @ sk_E))),
% 2.54/2.73      inference('sup-', [status(thm)], ['69', '70'])).
% 2.54/2.73  thf('72', plain, ((v1_relat_1 @ sk_E)),
% 2.54/2.73      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.73  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('74', plain, ((v2_funct_1 @ sk_E)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('75', plain,
% 2.54/2.73      (![X0 : $i]:
% 2.54/2.73         (~ (r1_tarski @ X0 @ sk_B)
% 2.54/2.73          | ((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ X0)) = (X0)))),
% 2.54/2.73      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 2.54/2.73  thf('76', plain,
% 2.54/2.73      (((k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 2.54/2.73         = (k2_relat_1 @ sk_D))),
% 2.54/2.73      inference('sup-', [status(thm)], ['68', '75'])).
% 2.54/2.73  thf(t160_relat_1, axiom,
% 2.54/2.73    (![A:$i]:
% 2.54/2.73     ( ( v1_relat_1 @ A ) =>
% 2.54/2.73       ( ![B:$i]:
% 2.54/2.73         ( ( v1_relat_1 @ B ) =>
% 2.54/2.73           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.54/2.73             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.54/2.73  thf('77', plain,
% 2.54/2.73      (![X10 : $i, X11 : $i]:
% 2.54/2.73         (~ (v1_relat_1 @ X10)
% 2.54/2.73          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 2.54/2.73              = (k9_relat_1 @ X10 @ (k2_relat_1 @ X11)))
% 2.54/2.73          | ~ (v1_relat_1 @ X11))),
% 2.54/2.73      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.54/2.73  thf('78', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('79', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(dt_k4_relset_1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.54/2.73     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.54/2.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.54/2.73       ( m1_subset_1 @
% 2.54/2.73         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.54/2.73         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.54/2.73  thf('80', plain,
% 2.54/2.73      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.54/2.73         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.54/2.73          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.54/2.73          | (m1_subset_1 @ (k4_relset_1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 2.54/2.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 2.54/2.73      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.54/2.73  thf('81', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.73         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.54/2.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.54/2.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['79', '80'])).
% 2.54/2.73  thf('82', plain,
% 2.54/2.73      ((m1_subset_1 @ 
% 2.54/2.73        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.54/2.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['78', '81'])).
% 2.54/2.73  thf('83', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('84', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(redefinition_k4_relset_1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.54/2.73     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.54/2.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.54/2.73       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.54/2.73  thf('85', plain,
% 2.54/2.73      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.54/2.73         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.54/2.73          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 2.54/2.73          | ((k4_relset_1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 2.54/2.73              = (k5_relat_1 @ X39 @ X42)))),
% 2.54/2.73      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.54/2.73  thf('86', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.73         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.54/2.73            = (k5_relat_1 @ sk_D @ X0))
% 2.54/2.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.54/2.73      inference('sup-', [status(thm)], ['84', '85'])).
% 2.54/2.73  thf('87', plain,
% 2.54/2.73      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.54/2.73         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.54/2.73      inference('sup-', [status(thm)], ['83', '86'])).
% 2.54/2.73  thf('88', plain,
% 2.54/2.73      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.54/2.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.54/2.73      inference('demod', [status(thm)], ['82', '87'])).
% 2.54/2.73  thf('89', plain,
% 2.54/2.73      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.54/2.73         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 2.54/2.73          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 2.54/2.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.54/2.73  thf('90', plain,
% 2.54/2.73      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.54/2.73         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['88', '89'])).
% 2.54/2.73  thf('91', plain,
% 2.54/2.73      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.54/2.73         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('92', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('93', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf(redefinition_k1_partfun1, axiom,
% 2.54/2.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.54/2.73     ( ( ( v1_funct_1 @ E ) & 
% 2.54/2.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.54/2.73         ( v1_funct_1 @ F ) & 
% 2.54/2.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.54/2.73       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.54/2.73  thf('94', plain,
% 2.54/2.73      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 2.54/2.73         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 2.54/2.73          | ~ (v1_funct_1 @ X53)
% 2.54/2.73          | ~ (v1_funct_1 @ X56)
% 2.54/2.73          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 2.54/2.73          | ((k1_partfun1 @ X54 @ X55 @ X57 @ X58 @ X53 @ X56)
% 2.54/2.73              = (k5_relat_1 @ X53 @ X56)))),
% 2.54/2.73      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.54/2.73  thf('95', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.73         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.54/2.73            = (k5_relat_1 @ sk_D @ X0))
% 2.54/2.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.54/2.73          | ~ (v1_funct_1 @ X0)
% 2.54/2.73          | ~ (v1_funct_1 @ sk_D))),
% 2.54/2.73      inference('sup-', [status(thm)], ['93', '94'])).
% 2.54/2.73  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('97', plain,
% 2.54/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.73         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.54/2.73            = (k5_relat_1 @ sk_D @ X0))
% 2.54/2.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.54/2.73          | ~ (v1_funct_1 @ X0))),
% 2.54/2.73      inference('demod', [status(thm)], ['95', '96'])).
% 2.54/2.73  thf('98', plain,
% 2.54/2.73      ((~ (v1_funct_1 @ sk_E)
% 2.54/2.73        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.54/2.73            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.54/2.73      inference('sup-', [status(thm)], ['92', '97'])).
% 2.54/2.73  thf('99', plain, ((v1_funct_1 @ sk_E)),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('100', plain,
% 2.54/2.73      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.54/2.73         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.54/2.73      inference('demod', [status(thm)], ['98', '99'])).
% 2.54/2.73  thf('101', plain,
% 2.54/2.73      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.54/2.73      inference('demod', [status(thm)], ['91', '100'])).
% 2.54/2.73  thf('102', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.54/2.73      inference('sup+', [status(thm)], ['90', '101'])).
% 2.54/2.73  thf('103', plain,
% 2.54/2.73      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 2.54/2.73        | ~ (v1_relat_1 @ sk_D)
% 2.54/2.73        | ~ (v1_relat_1 @ sk_E))),
% 2.54/2.73      inference('sup+', [status(thm)], ['77', '102'])).
% 2.54/2.73  thf('104', plain,
% 2.54/2.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('105', plain,
% 2.54/2.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.54/2.73         ((v1_relat_1 @ X18)
% 2.54/2.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.54/2.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.54/2.73  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 2.54/2.73      inference('sup-', [status(thm)], ['104', '105'])).
% 2.54/2.73  thf('107', plain, ((v1_relat_1 @ sk_E)),
% 2.54/2.73      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.73  thf('108', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 2.54/2.73      inference('demod', [status(thm)], ['103', '106', '107'])).
% 2.54/2.73  thf('109', plain, (((k10_relat_1 @ sk_E @ sk_C) = (k2_relat_1 @ sk_D))),
% 2.54/2.73      inference('demod', [status(thm)], ['76', '108'])).
% 2.54/2.73  thf('110', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 2.54/2.73      inference('sup+', [status(thm)], ['59', '109'])).
% 2.54/2.73  thf('111', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 2.54/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.73  thf('112', plain,
% 2.54/2.73      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.54/2.73      inference('sup-', [status(thm)], ['63', '64'])).
% 2.54/2.73  thf('113', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 2.54/2.73      inference('demod', [status(thm)], ['111', '112'])).
% 2.54/2.73  thf('114', plain, ($false),
% 2.54/2.73      inference('simplify_reflect-', [status(thm)], ['110', '113'])).
% 2.54/2.73  
% 2.54/2.73  % SZS output end Refutation
% 2.54/2.73  
% 2.54/2.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
