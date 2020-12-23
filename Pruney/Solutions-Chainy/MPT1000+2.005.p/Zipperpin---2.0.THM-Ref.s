%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fYLgq2VdzK

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:58 EST 2020

% Result     : Theorem 9.04s
% Output     : Refutation 9.04s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 259 expanded)
%              Number of leaves         :   42 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  896 (2677 expanded)
%              Number of equality atoms :  108 ( 297 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t48_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ B )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_funct_2])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('4',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_B_1 )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k8_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k10_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ X0 )
      = ( k10_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k10_relat_1 @ sk_C_2 @ sk_B_1 )
 != sk_A ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['34','39'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('41',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k5_relat_1 @ sk_C_2 @ ( k6_relat_1 @ sk_B_1 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['37','38'])).

thf('44',plain,
    ( ( k5_relat_1 @ sk_C_2 @ ( k6_relat_1 @ sk_B_1 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['42','43'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('45',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X26 @ X25 ) )
        = ( k10_relat_1 @ X26 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( k10_relat_1 @ sk_C_2 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['37','38'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = ( k10_relat_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k1_relat_1 @ sk_C_2 )
 != sk_A ),
    inference(demod,[status(thm)],['29','52'])).

thf('54',plain,
    ( $false
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = ( k10_relat_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ X0 )
      = ( k10_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('59',plain,(
    ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_B_1 )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_B_1 )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('62',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_B_1 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( ( ( k10_relat_1 @ sk_C_2 @ sk_B_1 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,
    ( ( ( k10_relat_1 @ sk_C_2 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('70',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('71',plain,
    ( ( v1_funct_2 @ sk_C_2 @ k1_xboole_0 @ sk_B_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('73',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('78',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_C_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('81',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('82',plain,
    ( ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X44 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X43: $i] :
      ( zip_tseitin_0 @ X43 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','84'])).

thf('86',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','85'])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('90',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['54','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fYLgq2VdzK
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:46:48 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 9.04/9.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.04/9.23  % Solved by: fo/fo7.sh
% 9.04/9.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.04/9.23  % done 7414 iterations in 8.766s
% 9.04/9.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.04/9.23  % SZS output start Refutation
% 9.04/9.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.04/9.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.04/9.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.04/9.23  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 9.04/9.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.04/9.23  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 9.04/9.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 9.04/9.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 9.04/9.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.04/9.23  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.04/9.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.04/9.23  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.04/9.23  thf(sk_A_type, type, sk_A: $i).
% 9.04/9.23  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 9.04/9.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.04/9.23  thf(sk_C_2_type, type, sk_C_2: $i).
% 9.04/9.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.04/9.23  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.04/9.23  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.04/9.23  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.04/9.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.04/9.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.04/9.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.04/9.23  thf(d1_funct_2, axiom,
% 9.04/9.23    (![A:$i,B:$i,C:$i]:
% 9.04/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.04/9.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.04/9.23           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 9.04/9.23             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 9.04/9.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.04/9.23           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 9.04/9.23             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 9.04/9.23  thf(zf_stmt_0, axiom,
% 9.04/9.23    (![B:$i,A:$i]:
% 9.04/9.23     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.04/9.23       ( zip_tseitin_0 @ B @ A ) ))).
% 9.04/9.23  thf('0', plain,
% 9.04/9.23      (![X43 : $i, X44 : $i]:
% 9.04/9.23         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.04/9.23  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 9.04/9.23  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.04/9.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.04/9.23  thf('2', plain,
% 9.04/9.23      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 9.04/9.23      inference('sup+', [status(thm)], ['0', '1'])).
% 9.04/9.23  thf(t48_funct_2, conjecture,
% 9.04/9.23    (![A:$i,B:$i,C:$i]:
% 9.04/9.23     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.04/9.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.04/9.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.04/9.23         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 9.04/9.23  thf(zf_stmt_1, negated_conjecture,
% 9.04/9.23    (~( ![A:$i,B:$i,C:$i]:
% 9.04/9.23        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.04/9.23            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.04/9.23          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.04/9.23            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ) )),
% 9.04/9.23    inference('cnf.neg', [status(esa)], [t48_funct_2])).
% 9.04/9.23  thf('3', plain,
% 9.04/9.23      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 9.04/9.23  thf(zf_stmt_3, axiom,
% 9.04/9.23    (![C:$i,B:$i,A:$i]:
% 9.04/9.23     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 9.04/9.23       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 9.04/9.23  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 9.04/9.23  thf(zf_stmt_5, axiom,
% 9.04/9.23    (![A:$i,B:$i,C:$i]:
% 9.04/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.04/9.23       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 9.04/9.23         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.04/9.23           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 9.04/9.23             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 9.04/9.23  thf('4', plain,
% 9.04/9.23      (![X48 : $i, X49 : $i, X50 : $i]:
% 9.04/9.23         (~ (zip_tseitin_0 @ X48 @ X49)
% 9.04/9.23          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 9.04/9.23          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.04/9.23  thf('5', plain,
% 9.04/9.23      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 9.04/9.23        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 9.04/9.23      inference('sup-', [status(thm)], ['3', '4'])).
% 9.04/9.23  thf('6', plain,
% 9.04/9.23      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 9.04/9.23      inference('sup-', [status(thm)], ['2', '5'])).
% 9.04/9.23  thf('7', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf('8', plain,
% 9.04/9.23      (![X45 : $i, X46 : $i, X47 : $i]:
% 9.04/9.23         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 9.04/9.23          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 9.04/9.23          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 9.04/9.23  thf('9', plain,
% 9.04/9.23      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 9.04/9.23        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 9.04/9.23      inference('sup-', [status(thm)], ['7', '8'])).
% 9.04/9.23  thf('10', plain,
% 9.04/9.23      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf(redefinition_k1_relset_1, axiom,
% 9.04/9.23    (![A:$i,B:$i,C:$i]:
% 9.04/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.04/9.23       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 9.04/9.23  thf('11', plain,
% 9.04/9.23      (![X36 : $i, X37 : $i, X38 : $i]:
% 9.04/9.23         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 9.04/9.23          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 9.04/9.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.04/9.23  thf('12', plain,
% 9.04/9.23      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 9.04/9.23      inference('sup-', [status(thm)], ['10', '11'])).
% 9.04/9.23  thf('13', plain,
% 9.04/9.23      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 9.04/9.23        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 9.04/9.23      inference('demod', [status(thm)], ['9', '12'])).
% 9.04/9.23  thf('14', plain,
% 9.04/9.23      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 9.04/9.23      inference('sup-', [status(thm)], ['6', '13'])).
% 9.04/9.23  thf(l13_xboole_0, axiom,
% 9.04/9.23    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 9.04/9.23  thf('15', plain,
% 9.04/9.23      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 9.04/9.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 9.04/9.23  thf('16', plain,
% 9.04/9.23      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 9.04/9.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 9.04/9.23  thf('17', plain,
% 9.04/9.23      (![X0 : $i, X1 : $i]:
% 9.04/9.23         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 9.04/9.23      inference('sup+', [status(thm)], ['15', '16'])).
% 9.04/9.23  thf('18', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf('19', plain,
% 9.04/9.23      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 9.04/9.23      inference('split', [status(esa)], ['18'])).
% 9.04/9.23  thf('20', plain,
% 9.04/9.23      ((![X0 : $i]:
% 9.04/9.23          (((X0) != (k1_xboole_0))
% 9.04/9.23           | ~ (v1_xboole_0 @ X0)
% 9.04/9.23           | ~ (v1_xboole_0 @ sk_B_1)))
% 9.04/9.23         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['17', '19'])).
% 9.04/9.23  thf('21', plain,
% 9.04/9.23      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 9.04/9.23         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 9.04/9.23      inference('simplify', [status(thm)], ['20'])).
% 9.04/9.23  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.04/9.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.04/9.23  thf('23', plain,
% 9.04/9.23      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 9.04/9.23      inference('simplify_reflect+', [status(thm)], ['21', '22'])).
% 9.04/9.23  thf('24', plain,
% 9.04/9.23      ((((sk_A) = (k1_relat_1 @ sk_C_2))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['14', '23'])).
% 9.04/9.23  thf('25', plain,
% 9.04/9.23      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_B_1) != (sk_A))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf('26', plain,
% 9.04/9.23      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf(redefinition_k8_relset_1, axiom,
% 9.04/9.23    (![A:$i,B:$i,C:$i,D:$i]:
% 9.04/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.04/9.23       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 9.04/9.23  thf('27', plain,
% 9.04/9.23      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 9.04/9.23         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 9.04/9.23          | ((k8_relset_1 @ X40 @ X41 @ X39 @ X42) = (k10_relat_1 @ X39 @ X42)))),
% 9.04/9.23      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 9.04/9.23  thf('28', plain,
% 9.04/9.23      (![X0 : $i]:
% 9.04/9.23         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ X0)
% 9.04/9.23           = (k10_relat_1 @ sk_C_2 @ X0))),
% 9.04/9.23      inference('sup-', [status(thm)], ['26', '27'])).
% 9.04/9.23  thf('29', plain, (((k10_relat_1 @ sk_C_2 @ sk_B_1) != (sk_A))),
% 9.04/9.23      inference('demod', [status(thm)], ['25', '28'])).
% 9.04/9.23  thf('30', plain,
% 9.04/9.23      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf(cc2_relset_1, axiom,
% 9.04/9.23    (![A:$i,B:$i,C:$i]:
% 9.04/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.04/9.23       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 9.04/9.23  thf('31', plain,
% 9.04/9.23      (![X33 : $i, X34 : $i, X35 : $i]:
% 9.04/9.23         ((v5_relat_1 @ X33 @ X35)
% 9.04/9.23          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 9.04/9.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.04/9.23  thf('32', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 9.04/9.23      inference('sup-', [status(thm)], ['30', '31'])).
% 9.04/9.23  thf(d19_relat_1, axiom,
% 9.04/9.23    (![A:$i,B:$i]:
% 9.04/9.23     ( ( v1_relat_1 @ B ) =>
% 9.04/9.23       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 9.04/9.23  thf('33', plain,
% 9.04/9.23      (![X20 : $i, X21 : $i]:
% 9.04/9.23         (~ (v5_relat_1 @ X20 @ X21)
% 9.04/9.23          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 9.04/9.23          | ~ (v1_relat_1 @ X20))),
% 9.04/9.23      inference('cnf', [status(esa)], [d19_relat_1])).
% 9.04/9.23  thf('34', plain,
% 9.04/9.23      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 9.04/9.23      inference('sup-', [status(thm)], ['32', '33'])).
% 9.04/9.23  thf('35', plain,
% 9.04/9.23      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf(cc2_relat_1, axiom,
% 9.04/9.23    (![A:$i]:
% 9.04/9.23     ( ( v1_relat_1 @ A ) =>
% 9.04/9.23       ( ![B:$i]:
% 9.04/9.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 9.04/9.23  thf('36', plain,
% 9.04/9.23      (![X18 : $i, X19 : $i]:
% 9.04/9.23         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 9.04/9.23          | (v1_relat_1 @ X18)
% 9.04/9.23          | ~ (v1_relat_1 @ X19))),
% 9.04/9.23      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.04/9.23  thf('37', plain,
% 9.04/9.23      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_2))),
% 9.04/9.23      inference('sup-', [status(thm)], ['35', '36'])).
% 9.04/9.23  thf(fc6_relat_1, axiom,
% 9.04/9.23    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 9.04/9.23  thf('38', plain,
% 9.04/9.23      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 9.04/9.23      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.04/9.23  thf('39', plain, ((v1_relat_1 @ sk_C_2)),
% 9.04/9.23      inference('demod', [status(thm)], ['37', '38'])).
% 9.04/9.23  thf('40', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 9.04/9.23      inference('demod', [status(thm)], ['34', '39'])).
% 9.04/9.23  thf(t79_relat_1, axiom,
% 9.04/9.23    (![A:$i,B:$i]:
% 9.04/9.23     ( ( v1_relat_1 @ B ) =>
% 9.04/9.23       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 9.04/9.23         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 9.04/9.23  thf('41', plain,
% 9.04/9.23      (![X29 : $i, X30 : $i]:
% 9.04/9.23         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 9.04/9.23          | ((k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) = (X29))
% 9.04/9.23          | ~ (v1_relat_1 @ X29))),
% 9.04/9.23      inference('cnf', [status(esa)], [t79_relat_1])).
% 9.04/9.23  thf('42', plain,
% 9.04/9.23      ((~ (v1_relat_1 @ sk_C_2)
% 9.04/9.23        | ((k5_relat_1 @ sk_C_2 @ (k6_relat_1 @ sk_B_1)) = (sk_C_2)))),
% 9.04/9.23      inference('sup-', [status(thm)], ['40', '41'])).
% 9.04/9.23  thf('43', plain, ((v1_relat_1 @ sk_C_2)),
% 9.04/9.23      inference('demod', [status(thm)], ['37', '38'])).
% 9.04/9.23  thf('44', plain,
% 9.04/9.23      (((k5_relat_1 @ sk_C_2 @ (k6_relat_1 @ sk_B_1)) = (sk_C_2))),
% 9.04/9.23      inference('demod', [status(thm)], ['42', '43'])).
% 9.04/9.23  thf(t71_relat_1, axiom,
% 9.04/9.23    (![A:$i]:
% 9.04/9.23     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 9.04/9.23       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 9.04/9.23  thf('45', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 9.04/9.23      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.04/9.23  thf(t182_relat_1, axiom,
% 9.04/9.23    (![A:$i]:
% 9.04/9.23     ( ( v1_relat_1 @ A ) =>
% 9.04/9.23       ( ![B:$i]:
% 9.04/9.23         ( ( v1_relat_1 @ B ) =>
% 9.04/9.23           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 9.04/9.23             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 9.04/9.23  thf('46', plain,
% 9.04/9.23      (![X25 : $i, X26 : $i]:
% 9.04/9.23         (~ (v1_relat_1 @ X25)
% 9.04/9.23          | ((k1_relat_1 @ (k5_relat_1 @ X26 @ X25))
% 9.04/9.23              = (k10_relat_1 @ X26 @ (k1_relat_1 @ X25)))
% 9.04/9.23          | ~ (v1_relat_1 @ X26))),
% 9.04/9.23      inference('cnf', [status(esa)], [t182_relat_1])).
% 9.04/9.23  thf('47', plain,
% 9.04/9.23      (![X0 : $i, X1 : $i]:
% 9.04/9.23         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.04/9.23            = (k10_relat_1 @ X1 @ X0))
% 9.04/9.23          | ~ (v1_relat_1 @ X1)
% 9.04/9.23          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.04/9.23      inference('sup+', [status(thm)], ['45', '46'])).
% 9.04/9.23  thf(fc3_funct_1, axiom,
% 9.04/9.23    (![A:$i]:
% 9.04/9.23     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 9.04/9.23       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 9.04/9.23  thf('48', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 9.04/9.23      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.04/9.23  thf('49', plain,
% 9.04/9.23      (![X0 : $i, X1 : $i]:
% 9.04/9.23         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.04/9.23            = (k10_relat_1 @ X1 @ X0))
% 9.04/9.23          | ~ (v1_relat_1 @ X1))),
% 9.04/9.23      inference('demod', [status(thm)], ['47', '48'])).
% 9.04/9.23  thf('50', plain,
% 9.04/9.23      ((((k1_relat_1 @ sk_C_2) = (k10_relat_1 @ sk_C_2 @ sk_B_1))
% 9.04/9.23        | ~ (v1_relat_1 @ sk_C_2))),
% 9.04/9.23      inference('sup+', [status(thm)], ['44', '49'])).
% 9.04/9.23  thf('51', plain, ((v1_relat_1 @ sk_C_2)),
% 9.04/9.23      inference('demod', [status(thm)], ['37', '38'])).
% 9.04/9.23  thf('52', plain, (((k1_relat_1 @ sk_C_2) = (k10_relat_1 @ sk_C_2 @ sk_B_1))),
% 9.04/9.23      inference('demod', [status(thm)], ['50', '51'])).
% 9.04/9.23  thf('53', plain, (((k1_relat_1 @ sk_C_2) != (sk_A))),
% 9.04/9.23      inference('demod', [status(thm)], ['29', '52'])).
% 9.04/9.23  thf('54', plain, (($false) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 9.04/9.23      inference('simplify_reflect-', [status(thm)], ['24', '53'])).
% 9.04/9.23  thf('55', plain, (((k1_relat_1 @ sk_C_2) = (k10_relat_1 @ sk_C_2 @ sk_B_1))),
% 9.04/9.23      inference('demod', [status(thm)], ['50', '51'])).
% 9.04/9.23  thf('56', plain,
% 9.04/9.23      (![X0 : $i]:
% 9.04/9.23         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ X0)
% 9.04/9.23           = (k10_relat_1 @ sk_C_2 @ X0))),
% 9.04/9.23      inference('sup-', [status(thm)], ['26', '27'])).
% 9.04/9.23  thf('57', plain,
% 9.04/9.23      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 9.04/9.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 9.04/9.23  thf('58', plain,
% 9.04/9.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('split', [status(esa)], ['18'])).
% 9.04/9.23  thf('59', plain,
% 9.04/9.23      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_B_1) != (sk_A))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf('60', plain,
% 9.04/9.23      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_B_1) != (sk_A)))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['58', '59'])).
% 9.04/9.23  thf('61', plain,
% 9.04/9.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('split', [status(esa)], ['18'])).
% 9.04/9.23  thf('62', plain,
% 9.04/9.23      ((((k8_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_B_1)
% 9.04/9.23          != (k1_xboole_0)))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('demod', [status(thm)], ['60', '61'])).
% 9.04/9.23  thf('63', plain,
% 9.04/9.23      ((![X0 : $i]:
% 9.04/9.23          (((k8_relset_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_B_1) != (k1_xboole_0))
% 9.04/9.23           | ~ (v1_xboole_0 @ X0)))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['57', '62'])).
% 9.04/9.23  thf('64', plain,
% 9.04/9.23      (((((k10_relat_1 @ sk_C_2 @ sk_B_1) != (k1_xboole_0))
% 9.04/9.23         | ~ (v1_xboole_0 @ sk_A))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['56', '63'])).
% 9.04/9.23  thf('65', plain,
% 9.04/9.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('split', [status(esa)], ['18'])).
% 9.04/9.23  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.04/9.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.04/9.23  thf('67', plain,
% 9.04/9.23      ((((k10_relat_1 @ sk_C_2 @ sk_B_1) != (k1_xboole_0)))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('demod', [status(thm)], ['64', '65', '66'])).
% 9.04/9.23  thf('68', plain,
% 9.04/9.23      ((((k1_relat_1 @ sk_C_2) != (k1_xboole_0)))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['55', '67'])).
% 9.04/9.23  thf('69', plain,
% 9.04/9.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('split', [status(esa)], ['18'])).
% 9.04/9.23  thf('70', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf('71', plain,
% 9.04/9.23      (((v1_funct_2 @ sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup+', [status(thm)], ['69', '70'])).
% 9.04/9.23  thf('72', plain,
% 9.04/9.23      (![X45 : $i, X46 : $i, X47 : $i]:
% 9.04/9.23         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 9.04/9.23          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 9.04/9.23          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 9.04/9.23  thf('73', plain,
% 9.04/9.23      (((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ k1_xboole_0)
% 9.04/9.23         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2))))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['71', '72'])).
% 9.04/9.23  thf('74', plain,
% 9.04/9.23      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('split', [status(esa)], ['18'])).
% 9.04/9.23  thf('75', plain,
% 9.04/9.23      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.04/9.23  thf('76', plain,
% 9.04/9.23      (((m1_subset_1 @ sk_C_2 @ 
% 9.04/9.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup+', [status(thm)], ['74', '75'])).
% 9.04/9.23  thf('77', plain,
% 9.04/9.23      (![X36 : $i, X37 : $i, X38 : $i]:
% 9.04/9.23         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 9.04/9.23          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 9.04/9.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.04/9.23  thf('78', plain,
% 9.04/9.23      ((((k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['76', '77'])).
% 9.04/9.23  thf('79', plain,
% 9.04/9.23      (((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ k1_xboole_0)
% 9.04/9.23         | ((k1_xboole_0) = (k1_relat_1 @ sk_C_2))))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('demod', [status(thm)], ['73', '78'])).
% 9.04/9.23  thf('80', plain,
% 9.04/9.23      (((m1_subset_1 @ sk_C_2 @ 
% 9.04/9.23         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup+', [status(thm)], ['74', '75'])).
% 9.04/9.23  thf('81', plain,
% 9.04/9.23      (![X48 : $i, X49 : $i, X50 : $i]:
% 9.04/9.23         (~ (zip_tseitin_0 @ X48 @ X49)
% 9.04/9.23          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 9.04/9.23          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.04/9.23  thf('82', plain,
% 9.04/9.23      ((((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ k1_xboole_0)
% 9.04/9.23         | ~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('sup-', [status(thm)], ['80', '81'])).
% 9.04/9.23  thf('83', plain,
% 9.04/9.23      (![X43 : $i, X44 : $i]:
% 9.04/9.23         ((zip_tseitin_0 @ X43 @ X44) | ((X44) != (k1_xboole_0)))),
% 9.04/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.04/9.23  thf('84', plain, (![X43 : $i]: (zip_tseitin_0 @ X43 @ k1_xboole_0)),
% 9.04/9.23      inference('simplify', [status(thm)], ['83'])).
% 9.04/9.23  thf('85', plain,
% 9.04/9.23      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ k1_xboole_0))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('demod', [status(thm)], ['82', '84'])).
% 9.04/9.23  thf('86', plain,
% 9.04/9.23      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_2)))
% 9.04/9.23         <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('demod', [status(thm)], ['79', '85'])).
% 9.04/9.23  thf('87', plain,
% 9.04/9.23      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 9.04/9.23      inference('demod', [status(thm)], ['68', '86'])).
% 9.04/9.23  thf('88', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 9.04/9.23      inference('simplify', [status(thm)], ['87'])).
% 9.04/9.23  thf('89', plain,
% 9.04/9.23      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 9.04/9.23      inference('split', [status(esa)], ['18'])).
% 9.04/9.23  thf('90', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 9.04/9.23      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 9.04/9.23  thf('91', plain, ($false),
% 9.04/9.23      inference('simpl_trail', [status(thm)], ['54', '90'])).
% 9.04/9.23  
% 9.04/9.23  % SZS output end Refutation
% 9.04/9.23  
% 9.04/9.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
