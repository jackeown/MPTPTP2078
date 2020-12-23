%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9hVfCSKyby

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:57 EST 2020

% Result     : Theorem 5.45s
% Output     : Refutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 460 expanded)
%              Number of leaves         :   47 ( 154 expanded)
%              Depth                    :   14
%              Number of atoms          : 1254 (9807 expanded)
%              Number of equality atoms :   81 ( 599 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X13 ) @ ( k9_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ sk_B ) )
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','20','21','24'])).

thf('26',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_B )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['26','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k2_relat_1 @ sk_E ) )
    = sk_B ),
    inference(demod,[status(thm)],['25','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45','54'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['66','67'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('69',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('72',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['57','60'])).

thf('74',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['65','72','73','74','77'])).

thf('79',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['37','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('86',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('88',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X13 ) @ ( k9_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v2_funct_1 @ sk_E )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('91',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('95',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('96',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['57','60'])).

thf('97',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('99',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('100',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['94','100'])).

thf('102',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['79','101'])).

thf('103',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('106',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['103','106'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9hVfCSKyby
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 5.45/5.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.45/5.64  % Solved by: fo/fo7.sh
% 5.45/5.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.45/5.64  % done 1222 iterations in 5.172s
% 5.45/5.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.45/5.64  % SZS output start Refutation
% 5.45/5.64  thf(sk_E_type, type, sk_E: $i).
% 5.45/5.64  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.45/5.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.45/5.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.45/5.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.45/5.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.45/5.64  thf(sk_C_type, type, sk_C: $i).
% 5.45/5.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.45/5.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.45/5.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.45/5.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.45/5.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.45/5.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.45/5.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.45/5.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.45/5.64  thf(sk_A_type, type, sk_A: $i).
% 5.45/5.64  thf(sk_B_type, type, sk_B: $i).
% 5.45/5.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.45/5.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.45/5.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.45/5.64  thf(sk_D_type, type, sk_D: $i).
% 5.45/5.64  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.45/5.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.45/5.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.45/5.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.45/5.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.45/5.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.45/5.64  thf(t28_funct_2, conjecture,
% 5.45/5.64    (![A:$i,B:$i,C:$i,D:$i]:
% 5.45/5.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.45/5.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.45/5.64       ( ![E:$i]:
% 5.45/5.64         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.45/5.64             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.45/5.64           ( ( ( ( k2_relset_1 @
% 5.45/5.64                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 5.45/5.64                 ( C ) ) & 
% 5.45/5.64               ( v2_funct_1 @ E ) ) =>
% 5.45/5.64             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 5.45/5.64               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 5.45/5.64  thf(zf_stmt_0, negated_conjecture,
% 5.45/5.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.45/5.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.45/5.64            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.45/5.64          ( ![E:$i]:
% 5.45/5.64            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.45/5.64                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.45/5.64              ( ( ( ( k2_relset_1 @
% 5.45/5.64                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 5.45/5.64                    ( C ) ) & 
% 5.45/5.64                  ( v2_funct_1 @ E ) ) =>
% 5.45/5.64                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 5.45/5.64                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 5.45/5.64    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 5.45/5.64  thf('0', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf(d1_funct_2, axiom,
% 5.45/5.64    (![A:$i,B:$i,C:$i]:
% 5.45/5.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.45/5.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.45/5.64           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.45/5.64             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.45/5.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.45/5.64           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.45/5.64             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.45/5.64  thf(zf_stmt_1, axiom,
% 5.45/5.64    (![C:$i,B:$i,A:$i]:
% 5.45/5.64     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.45/5.64       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.45/5.64  thf('1', plain,
% 5.45/5.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.45/5.64         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 5.45/5.64          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 5.45/5.64          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.45/5.64  thf('2', plain,
% 5.45/5.64      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 5.45/5.64        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 5.45/5.64      inference('sup-', [status(thm)], ['0', '1'])).
% 5.45/5.64  thf(zf_stmt_2, axiom,
% 5.45/5.64    (![B:$i,A:$i]:
% 5.45/5.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.45/5.64       ( zip_tseitin_0 @ B @ A ) ))).
% 5.45/5.64  thf('3', plain,
% 5.45/5.64      (![X26 : $i, X27 : $i]:
% 5.45/5.64         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.45/5.64  thf('4', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.45/5.64  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.45/5.64  thf(zf_stmt_5, axiom,
% 5.45/5.64    (![A:$i,B:$i,C:$i]:
% 5.45/5.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.45/5.64       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.45/5.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.45/5.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.45/5.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.45/5.64  thf('5', plain,
% 5.45/5.64      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.45/5.64         (~ (zip_tseitin_0 @ X31 @ X32)
% 5.45/5.64          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 5.45/5.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.45/5.64  thf('6', plain,
% 5.45/5.64      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 5.45/5.64      inference('sup-', [status(thm)], ['4', '5'])).
% 5.45/5.64  thf('7', plain,
% 5.45/5.64      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 5.45/5.64      inference('sup-', [status(thm)], ['3', '6'])).
% 5.45/5.64  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('9', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 5.45/5.64      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 5.45/5.64  thf('10', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf(redefinition_k1_relset_1, axiom,
% 5.45/5.64    (![A:$i,B:$i,C:$i]:
% 5.45/5.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.45/5.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.45/5.64  thf('11', plain,
% 5.45/5.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.45/5.64         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 5.45/5.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.45/5.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.45/5.64  thf('12', plain,
% 5.45/5.64      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 5.45/5.64      inference('sup-', [status(thm)], ['10', '11'])).
% 5.45/5.64  thf('13', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 5.45/5.64      inference('demod', [status(thm)], ['2', '9', '12'])).
% 5.45/5.64  thf(d10_xboole_0, axiom,
% 5.45/5.64    (![A:$i,B:$i]:
% 5.45/5.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.45/5.64  thf('14', plain,
% 5.45/5.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.45/5.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.45/5.64  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.45/5.64      inference('simplify', [status(thm)], ['14'])).
% 5.45/5.64  thf(t177_funct_1, axiom,
% 5.45/5.64    (![A:$i]:
% 5.45/5.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.45/5.64       ( ![B:$i]:
% 5.45/5.64         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 5.45/5.64           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 5.45/5.64             ( B ) ) ) ) ))).
% 5.45/5.64  thf('16', plain,
% 5.45/5.64      (![X12 : $i, X13 : $i]:
% 5.45/5.64         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 5.45/5.64          | ((k9_relat_1 @ (k2_funct_1 @ X13) @ (k9_relat_1 @ X13 @ X12))
% 5.45/5.64              = (X12))
% 5.45/5.64          | ~ (v2_funct_1 @ X13)
% 5.45/5.64          | ~ (v1_funct_1 @ X13)
% 5.45/5.64          | ~ (v1_relat_1 @ X13))),
% 5.45/5.64      inference('cnf', [status(esa)], [t177_funct_1])).
% 5.45/5.64  thf('17', plain,
% 5.45/5.64      (![X0 : $i]:
% 5.45/5.64         (~ (v1_relat_1 @ X0)
% 5.45/5.64          | ~ (v1_funct_1 @ X0)
% 5.45/5.64          | ~ (v2_funct_1 @ X0)
% 5.45/5.64          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 5.45/5.64              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 5.45/5.64      inference('sup-', [status(thm)], ['15', '16'])).
% 5.45/5.64  thf('18', plain,
% 5.45/5.64      ((((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ sk_B))
% 5.45/5.64          = (k1_relat_1 @ sk_E))
% 5.45/5.64        | ~ (v2_funct_1 @ sk_E)
% 5.45/5.64        | ~ (v1_funct_1 @ sk_E)
% 5.45/5.64        | ~ (v1_relat_1 @ sk_E))),
% 5.45/5.64      inference('sup+', [status(thm)], ['13', '17'])).
% 5.45/5.64  thf('19', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 5.45/5.64      inference('demod', [status(thm)], ['2', '9', '12'])).
% 5.45/5.64  thf('20', plain, ((v2_funct_1 @ sk_E)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('22', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf(cc1_relset_1, axiom,
% 5.45/5.64    (![A:$i,B:$i,C:$i]:
% 5.45/5.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.45/5.64       ( v1_relat_1 @ C ) ))).
% 5.45/5.64  thf('23', plain,
% 5.45/5.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.45/5.64         ((v1_relat_1 @ X14)
% 5.45/5.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 5.45/5.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.45/5.64  thf('24', plain, ((v1_relat_1 @ sk_E)),
% 5.45/5.64      inference('sup-', [status(thm)], ['22', '23'])).
% 5.45/5.64  thf('25', plain,
% 5.45/5.64      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ sk_B))
% 5.45/5.64         = (sk_B))),
% 5.45/5.64      inference('demod', [status(thm)], ['18', '19', '20', '21', '24'])).
% 5.45/5.64  thf('26', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 5.45/5.64      inference('demod', [status(thm)], ['2', '9', '12'])).
% 5.45/5.64  thf(t169_relat_1, axiom,
% 5.45/5.64    (![A:$i]:
% 5.45/5.64     ( ( v1_relat_1 @ A ) =>
% 5.45/5.64       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 5.45/5.64  thf('27', plain,
% 5.45/5.64      (![X7 : $i]:
% 5.45/5.64         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 5.45/5.64          | ~ (v1_relat_1 @ X7))),
% 5.45/5.64      inference('cnf', [status(esa)], [t169_relat_1])).
% 5.45/5.64  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.45/5.64      inference('simplify', [status(thm)], ['14'])).
% 5.45/5.64  thf(t147_funct_1, axiom,
% 5.45/5.64    (![A:$i,B:$i]:
% 5.45/5.64     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.45/5.64       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 5.45/5.64         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 5.45/5.64  thf('29', plain,
% 5.45/5.64      (![X10 : $i, X11 : $i]:
% 5.45/5.64         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 5.45/5.64          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 5.45/5.64          | ~ (v1_funct_1 @ X11)
% 5.45/5.64          | ~ (v1_relat_1 @ X11))),
% 5.45/5.64      inference('cnf', [status(esa)], [t147_funct_1])).
% 5.45/5.64  thf('30', plain,
% 5.45/5.64      (![X0 : $i]:
% 5.45/5.64         (~ (v1_relat_1 @ X0)
% 5.45/5.64          | ~ (v1_funct_1 @ X0)
% 5.45/5.64          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 5.45/5.64              = (k2_relat_1 @ X0)))),
% 5.45/5.64      inference('sup-', [status(thm)], ['28', '29'])).
% 5.45/5.64  thf('31', plain,
% 5.45/5.64      (![X0 : $i]:
% 5.45/5.64         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 5.45/5.64          | ~ (v1_relat_1 @ X0)
% 5.45/5.64          | ~ (v1_funct_1 @ X0)
% 5.45/5.64          | ~ (v1_relat_1 @ X0))),
% 5.45/5.64      inference('sup+', [status(thm)], ['27', '30'])).
% 5.45/5.64  thf('32', plain,
% 5.45/5.64      (![X0 : $i]:
% 5.45/5.64         (~ (v1_funct_1 @ X0)
% 5.45/5.64          | ~ (v1_relat_1 @ X0)
% 5.45/5.64          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 5.45/5.64      inference('simplify', [status(thm)], ['31'])).
% 5.45/5.64  thf('33', plain,
% 5.45/5.64      ((((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))
% 5.45/5.64        | ~ (v1_relat_1 @ sk_E)
% 5.45/5.64        | ~ (v1_funct_1 @ sk_E))),
% 5.45/5.64      inference('sup+', [status(thm)], ['26', '32'])).
% 5.45/5.64  thf('34', plain, ((v1_relat_1 @ sk_E)),
% 5.45/5.64      inference('sup-', [status(thm)], ['22', '23'])).
% 5.45/5.64  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('36', plain, (((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))),
% 5.45/5.64      inference('demod', [status(thm)], ['33', '34', '35'])).
% 5.45/5.64  thf('37', plain,
% 5.45/5.64      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k2_relat_1 @ sk_E)) = (sk_B))),
% 5.45/5.64      inference('demod', [status(thm)], ['25', '36'])).
% 5.45/5.64  thf('38', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('39', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf(dt_k1_partfun1, axiom,
% 5.45/5.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.45/5.64     ( ( ( v1_funct_1 @ E ) & 
% 5.45/5.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.45/5.64         ( v1_funct_1 @ F ) & 
% 5.45/5.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.45/5.64       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.45/5.64         ( m1_subset_1 @
% 5.45/5.64           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.45/5.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.45/5.64  thf('40', plain,
% 5.45/5.64      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 5.45/5.64         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 5.45/5.64          | ~ (v1_funct_1 @ X34)
% 5.45/5.64          | ~ (v1_funct_1 @ X37)
% 5.45/5.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 5.45/5.64          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 5.45/5.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 5.45/5.64      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.45/5.64  thf('41', plain,
% 5.45/5.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.45/5.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 5.45/5.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.45/5.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.45/5.64          | ~ (v1_funct_1 @ X1)
% 5.45/5.64          | ~ (v1_funct_1 @ sk_D))),
% 5.45/5.64      inference('sup-', [status(thm)], ['39', '40'])).
% 5.45/5.64  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('43', plain,
% 5.45/5.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.45/5.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 5.45/5.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.45/5.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.45/5.64          | ~ (v1_funct_1 @ X1))),
% 5.45/5.64      inference('demod', [status(thm)], ['41', '42'])).
% 5.45/5.64  thf('44', plain,
% 5.45/5.64      ((~ (v1_funct_1 @ sk_E)
% 5.45/5.64        | (m1_subset_1 @ 
% 5.45/5.64           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 5.45/5.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 5.45/5.64      inference('sup-', [status(thm)], ['38', '43'])).
% 5.45/5.64  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('46', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('47', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf(redefinition_k1_partfun1, axiom,
% 5.45/5.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.45/5.64     ( ( ( v1_funct_1 @ E ) & 
% 5.45/5.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.45/5.64         ( v1_funct_1 @ F ) & 
% 5.45/5.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.45/5.64       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.45/5.64  thf('48', plain,
% 5.45/5.64      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 5.45/5.64         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 5.45/5.64          | ~ (v1_funct_1 @ X40)
% 5.45/5.64          | ~ (v1_funct_1 @ X43)
% 5.45/5.64          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 5.45/5.64          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 5.45/5.64              = (k5_relat_1 @ X40 @ X43)))),
% 5.45/5.64      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.45/5.64  thf('49', plain,
% 5.45/5.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.45/5.64         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 5.45/5.64            = (k5_relat_1 @ sk_D @ X0))
% 5.45/5.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.45/5.64          | ~ (v1_funct_1 @ X0)
% 5.45/5.64          | ~ (v1_funct_1 @ sk_D))),
% 5.45/5.64      inference('sup-', [status(thm)], ['47', '48'])).
% 5.45/5.64  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('51', plain,
% 5.45/5.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.45/5.64         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 5.45/5.64            = (k5_relat_1 @ sk_D @ X0))
% 5.45/5.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.45/5.64          | ~ (v1_funct_1 @ X0))),
% 5.45/5.64      inference('demod', [status(thm)], ['49', '50'])).
% 5.45/5.64  thf('52', plain,
% 5.45/5.64      ((~ (v1_funct_1 @ sk_E)
% 5.45/5.64        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 5.45/5.64            = (k5_relat_1 @ sk_D @ sk_E)))),
% 5.45/5.64      inference('sup-', [status(thm)], ['46', '51'])).
% 5.45/5.64  thf('53', plain, ((v1_funct_1 @ sk_E)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('54', plain,
% 5.45/5.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 5.45/5.64         = (k5_relat_1 @ sk_D @ sk_E))),
% 5.45/5.64      inference('demod', [status(thm)], ['52', '53'])).
% 5.45/5.64  thf('55', plain,
% 5.45/5.64      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 5.45/5.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 5.45/5.64      inference('demod', [status(thm)], ['44', '45', '54'])).
% 5.45/5.64  thf(redefinition_k2_relset_1, axiom,
% 5.45/5.64    (![A:$i,B:$i,C:$i]:
% 5.45/5.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.45/5.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.45/5.64  thf('56', plain,
% 5.45/5.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.45/5.64         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 5.45/5.64          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 5.45/5.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.45/5.64  thf('57', plain,
% 5.45/5.64      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 5.45/5.64         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 5.45/5.64      inference('sup-', [status(thm)], ['55', '56'])).
% 5.45/5.64  thf('58', plain,
% 5.45/5.64      (((k2_relset_1 @ sk_A @ sk_C @ 
% 5.45/5.64         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('59', plain,
% 5.45/5.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 5.45/5.64         = (k5_relat_1 @ sk_D @ sk_E))),
% 5.45/5.64      inference('demod', [status(thm)], ['52', '53'])).
% 5.45/5.64  thf('60', plain,
% 5.45/5.64      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 5.45/5.64      inference('demod', [status(thm)], ['58', '59'])).
% 5.45/5.64  thf('61', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 5.45/5.64      inference('sup+', [status(thm)], ['57', '60'])).
% 5.45/5.64  thf(t45_relat_1, axiom,
% 5.45/5.64    (![A:$i]:
% 5.45/5.64     ( ( v1_relat_1 @ A ) =>
% 5.45/5.64       ( ![B:$i]:
% 5.45/5.64         ( ( v1_relat_1 @ B ) =>
% 5.45/5.64           ( r1_tarski @
% 5.45/5.64             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 5.45/5.64  thf('62', plain,
% 5.45/5.64      (![X8 : $i, X9 : $i]:
% 5.45/5.64         (~ (v1_relat_1 @ X8)
% 5.45/5.64          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 5.45/5.64             (k2_relat_1 @ X8))
% 5.45/5.64          | ~ (v1_relat_1 @ X9))),
% 5.45/5.64      inference('cnf', [status(esa)], [t45_relat_1])).
% 5.45/5.64  thf('63', plain,
% 5.45/5.64      (![X0 : $i, X2 : $i]:
% 5.45/5.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.45/5.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.45/5.64  thf('64', plain,
% 5.45/5.64      (![X0 : $i, X1 : $i]:
% 5.45/5.64         (~ (v1_relat_1 @ X1)
% 5.45/5.64          | ~ (v1_relat_1 @ X0)
% 5.45/5.64          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 5.45/5.64               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.45/5.64          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.45/5.64      inference('sup-', [status(thm)], ['62', '63'])).
% 5.45/5.64  thf('65', plain,
% 5.45/5.64      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 5.45/5.64        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 5.45/5.64        | ~ (v1_relat_1 @ sk_E)
% 5.45/5.64        | ~ (v1_relat_1 @ sk_D))),
% 5.45/5.64      inference('sup-', [status(thm)], ['61', '64'])).
% 5.45/5.64  thf('66', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf(cc2_relset_1, axiom,
% 5.45/5.64    (![A:$i,B:$i,C:$i]:
% 5.45/5.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.45/5.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.45/5.64  thf('67', plain,
% 5.45/5.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.45/5.64         ((v5_relat_1 @ X17 @ X19)
% 5.45/5.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.45/5.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.45/5.64  thf('68', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 5.45/5.64      inference('sup-', [status(thm)], ['66', '67'])).
% 5.45/5.64  thf(d19_relat_1, axiom,
% 5.45/5.64    (![A:$i,B:$i]:
% 5.45/5.64     ( ( v1_relat_1 @ B ) =>
% 5.45/5.64       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 5.45/5.64  thf('69', plain,
% 5.45/5.64      (![X3 : $i, X4 : $i]:
% 5.45/5.64         (~ (v5_relat_1 @ X3 @ X4)
% 5.45/5.64          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 5.45/5.64          | ~ (v1_relat_1 @ X3))),
% 5.45/5.64      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.45/5.64  thf('70', plain,
% 5.45/5.64      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 5.45/5.64      inference('sup-', [status(thm)], ['68', '69'])).
% 5.45/5.64  thf('71', plain, ((v1_relat_1 @ sk_E)),
% 5.45/5.64      inference('sup-', [status(thm)], ['22', '23'])).
% 5.45/5.64  thf('72', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 5.45/5.64      inference('demod', [status(thm)], ['70', '71'])).
% 5.45/5.64  thf('73', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 5.45/5.64      inference('sup+', [status(thm)], ['57', '60'])).
% 5.45/5.64  thf('74', plain, ((v1_relat_1 @ sk_E)),
% 5.45/5.64      inference('sup-', [status(thm)], ['22', '23'])).
% 5.45/5.64  thf('75', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('76', plain,
% 5.45/5.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.45/5.64         ((v1_relat_1 @ X14)
% 5.45/5.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 5.45/5.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.45/5.64  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 5.45/5.64      inference('sup-', [status(thm)], ['75', '76'])).
% 5.45/5.64  thf('78', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 5.45/5.64      inference('demod', [status(thm)], ['65', '72', '73', '74', '77'])).
% 5.45/5.64  thf('79', plain, (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) = (sk_B))),
% 5.45/5.64      inference('demod', [status(thm)], ['37', '78'])).
% 5.45/5.64  thf('80', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('81', plain,
% 5.45/5.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.45/5.64         ((v5_relat_1 @ X17 @ X19)
% 5.45/5.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.45/5.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.45/5.64  thf('82', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 5.45/5.64      inference('sup-', [status(thm)], ['80', '81'])).
% 5.45/5.64  thf('83', plain,
% 5.45/5.64      (![X3 : $i, X4 : $i]:
% 5.45/5.64         (~ (v5_relat_1 @ X3 @ X4)
% 5.45/5.64          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 5.45/5.64          | ~ (v1_relat_1 @ X3))),
% 5.45/5.64      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.45/5.64  thf('84', plain,
% 5.45/5.64      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 5.45/5.64      inference('sup-', [status(thm)], ['82', '83'])).
% 5.45/5.64  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 5.45/5.64      inference('sup-', [status(thm)], ['75', '76'])).
% 5.45/5.64  thf('86', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 5.45/5.64      inference('demod', [status(thm)], ['84', '85'])).
% 5.45/5.64  thf('87', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 5.45/5.64      inference('demod', [status(thm)], ['2', '9', '12'])).
% 5.45/5.64  thf('88', plain,
% 5.45/5.64      (![X12 : $i, X13 : $i]:
% 5.45/5.64         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 5.45/5.64          | ((k9_relat_1 @ (k2_funct_1 @ X13) @ (k9_relat_1 @ X13 @ X12))
% 5.45/5.64              = (X12))
% 5.45/5.64          | ~ (v2_funct_1 @ X13)
% 5.45/5.64          | ~ (v1_funct_1 @ X13)
% 5.45/5.64          | ~ (v1_relat_1 @ X13))),
% 5.45/5.64      inference('cnf', [status(esa)], [t177_funct_1])).
% 5.45/5.64  thf('89', plain,
% 5.45/5.64      (![X0 : $i]:
% 5.45/5.64         (~ (r1_tarski @ X0 @ sk_B)
% 5.45/5.64          | ~ (v1_relat_1 @ sk_E)
% 5.45/5.64          | ~ (v1_funct_1 @ sk_E)
% 5.45/5.64          | ~ (v2_funct_1 @ sk_E)
% 5.45/5.64          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0))
% 5.45/5.64              = (X0)))),
% 5.45/5.64      inference('sup-', [status(thm)], ['87', '88'])).
% 5.45/5.64  thf('90', plain, ((v1_relat_1 @ sk_E)),
% 5.45/5.64      inference('sup-', [status(thm)], ['22', '23'])).
% 5.45/5.64  thf('91', plain, ((v1_funct_1 @ sk_E)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('92', plain, ((v2_funct_1 @ sk_E)),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('93', plain,
% 5.45/5.64      (![X0 : $i]:
% 5.45/5.64         (~ (r1_tarski @ X0 @ sk_B)
% 5.45/5.64          | ((k9_relat_1 @ (k2_funct_1 @ sk_E) @ (k9_relat_1 @ sk_E @ X0))
% 5.45/5.64              = (X0)))),
% 5.45/5.64      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 5.45/5.64  thf('94', plain,
% 5.45/5.64      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ 
% 5.45/5.64         (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))) = (k2_relat_1 @ sk_D))),
% 5.45/5.64      inference('sup-', [status(thm)], ['86', '93'])).
% 5.45/5.64  thf(t160_relat_1, axiom,
% 5.45/5.64    (![A:$i]:
% 5.45/5.64     ( ( v1_relat_1 @ A ) =>
% 5.45/5.64       ( ![B:$i]:
% 5.45/5.64         ( ( v1_relat_1 @ B ) =>
% 5.45/5.64           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 5.45/5.64             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.45/5.64  thf('95', plain,
% 5.45/5.64      (![X5 : $i, X6 : $i]:
% 5.45/5.64         (~ (v1_relat_1 @ X5)
% 5.45/5.64          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 5.45/5.64              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 5.45/5.64          | ~ (v1_relat_1 @ X6))),
% 5.45/5.64      inference('cnf', [status(esa)], [t160_relat_1])).
% 5.45/5.64  thf('96', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 5.45/5.64      inference('sup+', [status(thm)], ['57', '60'])).
% 5.45/5.64  thf('97', plain,
% 5.45/5.64      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 5.45/5.64        | ~ (v1_relat_1 @ sk_D)
% 5.45/5.64        | ~ (v1_relat_1 @ sk_E))),
% 5.45/5.64      inference('sup+', [status(thm)], ['95', '96'])).
% 5.45/5.64  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 5.45/5.64      inference('sup-', [status(thm)], ['75', '76'])).
% 5.45/5.64  thf('99', plain, ((v1_relat_1 @ sk_E)),
% 5.45/5.64      inference('sup-', [status(thm)], ['22', '23'])).
% 5.45/5.64  thf('100', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 5.45/5.64      inference('demod', [status(thm)], ['97', '98', '99'])).
% 5.45/5.64  thf('101', plain,
% 5.45/5.64      (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) = (k2_relat_1 @ sk_D))),
% 5.45/5.64      inference('demod', [status(thm)], ['94', '100'])).
% 5.45/5.64  thf('102', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 5.45/5.64      inference('sup+', [status(thm)], ['79', '101'])).
% 5.45/5.64  thf('103', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('104', plain,
% 5.45/5.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.45/5.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.45/5.64  thf('105', plain,
% 5.45/5.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.45/5.64         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 5.45/5.64          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 5.45/5.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.45/5.64  thf('106', plain,
% 5.45/5.64      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.45/5.64      inference('sup-', [status(thm)], ['104', '105'])).
% 5.45/5.64  thf('107', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 5.45/5.64      inference('demod', [status(thm)], ['103', '106'])).
% 5.45/5.64  thf('108', plain, ($false),
% 5.45/5.64      inference('simplify_reflect-', [status(thm)], ['102', '107'])).
% 5.45/5.64  
% 5.45/5.64  % SZS output end Refutation
% 5.45/5.64  
% 5.45/5.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
