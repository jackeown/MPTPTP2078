%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sLW90qD0Ww

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:26 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 185 expanded)
%              Number of leaves         :   42 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  936 (3038 expanded)
%              Number of equality atoms :   66 ( 168 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t92_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ A )
        & ( v3_funct_2 @ C @ A @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r1_tarski @ B @ A )
       => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
            = B )
          & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
            = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ A )
          & ( v3_funct_2 @ C @ A @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r1_tarski @ B @ A )
         => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
              = B )
            & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
              = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t92_funct_2])).

thf('0',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
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

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X42 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('13',plain,(
    ! [X41: $i] :
      ( zip_tseitin_0 @ X41 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('16',plain,(
    zip_tseitin_1 @ sk_C @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['7','16'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v3_funct_2 @ X38 @ X39 @ X40 )
      | ( v2_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('28',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['19','24','25','31'])).

thf('33',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k8_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k10_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['35','38','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v3_funct_2 @ X38 @ X39 @ X40 )
      | ( v2_funct_2 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('46',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('50',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v2_funct_2 @ X50 @ X49 )
      | ( ( k2_relat_1 @ X50 )
        = X49 )
      | ~ ( v5_relat_1 @ X50 @ X49 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['51','52','55'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k2_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ X21 @ ( k10_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['43','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('65',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('66',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('71',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['42','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sLW90qD0Ww
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:27:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 575 iterations in 0.400s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.86  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.68/0.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.86  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.68/0.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.68/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.86  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.68/0.86  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.68/0.86  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.68/0.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.68/0.86  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.68/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.86  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.68/0.86  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.68/0.86  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.86  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.86  thf(t92_funct_2, conjecture,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.68/0.86         ( v3_funct_2 @ C @ A @ A ) & 
% 0.68/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.68/0.86       ( ( r1_tarski @ B @ A ) =>
% 0.68/0.86         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.68/0.86             ( B ) ) & 
% 0.68/0.86           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.68/0.86             ( B ) ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.86        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.68/0.86            ( v3_funct_2 @ C @ A @ A ) & 
% 0.68/0.86            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.68/0.86          ( ( r1_tarski @ B @ A ) =>
% 0.68/0.86            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.68/0.86                ( B ) ) & 
% 0.68/0.86              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.68/0.86                ( B ) ) ) ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.68/0.86  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('1', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(d1_funct_2, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.86           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.68/0.86             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.68/0.86         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.86           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.68/0.86             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_1, axiom,
% 0.68/0.86    (![C:$i,B:$i,A:$i]:
% 0.68/0.86     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.68/0.86       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.68/0.86         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.68/0.86          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.68/0.86          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.86  thf('3', plain,
% 0.68/0.86      ((~ (zip_tseitin_1 @ sk_C @ sk_A @ sk_A)
% 0.68/0.86        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(redefinition_k1_relset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.68/0.86  thf('5', plain,
% 0.68/0.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.68/0.86         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.68/0.86          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.68/0.86  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      ((~ (zip_tseitin_1 @ sk_C @ sk_A @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.68/0.86      inference('demod', [status(thm)], ['3', '6'])).
% 0.68/0.86  thf('8', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.68/0.86  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.68/0.86  thf(zf_stmt_4, axiom,
% 0.68/0.86    (![B:$i,A:$i]:
% 0.68/0.86     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.86       ( zip_tseitin_0 @ B @ A ) ))).
% 0.68/0.86  thf(zf_stmt_5, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.68/0.86         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.86           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.68/0.86             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.68/0.86  thf('9', plain,
% 0.68/0.86      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.68/0.86         (~ (zip_tseitin_0 @ X46 @ X47)
% 0.68/0.86          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 0.68/0.86          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.86  thf('10', plain,
% 0.68/0.86      (((zip_tseitin_1 @ sk_C @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      (![X41 : $i, X42 : $i]:
% 0.68/0.86         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.68/0.86  thf('12', plain,
% 0.68/0.86      (![X41 : $i, X42 : $i]:
% 0.68/0.86         ((zip_tseitin_0 @ X41 @ X42) | ((X42) != (k1_xboole_0)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.68/0.86  thf('13', plain, (![X41 : $i]: (zip_tseitin_0 @ X41 @ k1_xboole_0)),
% 0.68/0.86      inference('simplify', [status(thm)], ['12'])).
% 0.68/0.86  thf('14', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.68/0.86      inference('sup+', [status(thm)], ['11', '13'])).
% 0.68/0.86  thf('15', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.68/0.86      inference('eq_fact', [status(thm)], ['14'])).
% 0.68/0.86  thf('16', plain, ((zip_tseitin_1 @ sk_C @ sk_A @ sk_A)),
% 0.68/0.86      inference('demod', [status(thm)], ['10', '15'])).
% 0.68/0.86  thf('17', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.68/0.86      inference('demod', [status(thm)], ['7', '16'])).
% 0.68/0.86  thf(t164_funct_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.86       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.68/0.86         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.68/0.86  thf('18', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 0.68/0.86          | ~ (v2_funct_1 @ X23)
% 0.68/0.86          | ((k10_relat_1 @ X23 @ (k9_relat_1 @ X23 @ X22)) = (X22))
% 0.68/0.86          | ~ (v1_funct_1 @ X23)
% 0.68/0.86          | ~ (v1_relat_1 @ X23))),
% 0.68/0.86      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.68/0.86  thf('19', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X0 @ sk_A)
% 0.68/0.86          | ~ (v1_relat_1 @ sk_C)
% 0.68/0.86          | ~ (v1_funct_1 @ sk_C)
% 0.68/0.86          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.68/0.86          | ~ (v2_funct_1 @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['17', '18'])).
% 0.68/0.86  thf('20', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(cc2_relat_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( v1_relat_1 @ A ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.68/0.86          | (v1_relat_1 @ X14)
% 0.68/0.86          | ~ (v1_relat_1 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.68/0.86  thf('22', plain,
% 0.68/0.86      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.86  thf(fc6_relat_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.68/0.86  thf('23', plain,
% 0.68/0.86      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.68/0.86  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.86      inference('demod', [status(thm)], ['22', '23'])).
% 0.68/0.86  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('26', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(cc2_funct_2, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.68/0.86         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.68/0.86  thf('27', plain,
% 0.68/0.86      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X38)
% 0.68/0.86          | ~ (v3_funct_2 @ X38 @ X39 @ X40)
% 0.68/0.86          | (v2_funct_1 @ X38)
% 0.68/0.86          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.68/0.86      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.68/0.86  thf('28', plain,
% 0.68/0.86      (((v2_funct_1 @ sk_C)
% 0.68/0.86        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['26', '27'])).
% 0.68/0.86  thf('29', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('31', plain, ((v2_funct_1 @ sk_C)),
% 0.68/0.86      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.68/0.86  thf('32', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X0 @ sk_A)
% 0.68/0.86          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.68/0.86      inference('demod', [status(thm)], ['19', '24', '25', '31'])).
% 0.68/0.86  thf('33', plain,
% 0.68/0.86      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.68/0.86      inference('sup-', [status(thm)], ['0', '32'])).
% 0.68/0.86  thf('34', plain,
% 0.68/0.86      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.68/0.86        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('35', plain,
% 0.68/0.86      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.68/0.86         <= (~
% 0.68/0.86             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.68/0.86      inference('split', [status(esa)], ['34'])).
% 0.68/0.86  thf('36', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(redefinition_k7_relset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.68/0.86  thf('37', plain,
% 0.68/0.86      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.68/0.86          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.68/0.86  thf('38', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.86  thf('39', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(redefinition_k8_relset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.68/0.86  thf('40', plain,
% 0.68/0.86      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.68/0.86          | ((k8_relset_1 @ X35 @ X36 @ X34 @ X37) = (k10_relat_1 @ X34 @ X37)))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.68/0.86  thf('41', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['39', '40'])).
% 0.68/0.86  thf('42', plain,
% 0.68/0.86      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.68/0.86         <= (~
% 0.68/0.86             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.68/0.86      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.68/0.86  thf('43', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('44', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('45', plain,
% 0.68/0.86      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.68/0.86         (~ (v1_funct_1 @ X38)
% 0.68/0.86          | ~ (v3_funct_2 @ X38 @ X39 @ X40)
% 0.68/0.86          | (v2_funct_2 @ X38 @ X40)
% 0.68/0.86          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.68/0.86      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.68/0.86  thf('46', plain,
% 0.68/0.86      (((v2_funct_2 @ sk_C @ sk_A)
% 0.68/0.86        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['44', '45'])).
% 0.68/0.86  thf('47', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('49', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.68/0.86      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.68/0.86  thf(d3_funct_2, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.68/0.86       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.68/0.86  thf('50', plain,
% 0.68/0.86      (![X49 : $i, X50 : $i]:
% 0.68/0.86         (~ (v2_funct_2 @ X50 @ X49)
% 0.68/0.86          | ((k2_relat_1 @ X50) = (X49))
% 0.68/0.86          | ~ (v5_relat_1 @ X50 @ X49)
% 0.68/0.86          | ~ (v1_relat_1 @ X50))),
% 0.68/0.86      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.68/0.86  thf('51', plain,
% 0.68/0.86      ((~ (v1_relat_1 @ sk_C)
% 0.68/0.86        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.68/0.86        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['49', '50'])).
% 0.68/0.86  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.86      inference('demod', [status(thm)], ['22', '23'])).
% 0.68/0.86  thf('53', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(cc2_relset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.86       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.68/0.86  thf('54', plain,
% 0.68/0.86      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.68/0.86         ((v5_relat_1 @ X24 @ X26)
% 0.68/0.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.68/0.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.68/0.86  thf('55', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.68/0.86      inference('sup-', [status(thm)], ['53', '54'])).
% 0.68/0.86  thf('56', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['51', '52', '55'])).
% 0.68/0.86  thf(t147_funct_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.86       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.68/0.86         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.68/0.86  thf('57', plain,
% 0.68/0.86      (![X20 : $i, X21 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X20 @ (k2_relat_1 @ X21))
% 0.68/0.86          | ((k9_relat_1 @ X21 @ (k10_relat_1 @ X21 @ X20)) = (X20))
% 0.68/0.86          | ~ (v1_funct_1 @ X21)
% 0.68/0.86          | ~ (v1_relat_1 @ X21))),
% 0.68/0.86      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.68/0.86  thf('58', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X0 @ sk_A)
% 0.68/0.86          | ~ (v1_relat_1 @ sk_C)
% 0.68/0.86          | ~ (v1_funct_1 @ sk_C)
% 0.68/0.86          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['56', '57'])).
% 0.68/0.86  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.86      inference('demod', [status(thm)], ['22', '23'])).
% 0.68/0.86  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('61', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X0 @ sk_A)
% 0.68/0.86          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.68/0.86      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.68/0.86  thf('62', plain,
% 0.68/0.86      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.68/0.86      inference('sup-', [status(thm)], ['43', '61'])).
% 0.68/0.86  thf('63', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['39', '40'])).
% 0.68/0.86  thf('64', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.86  thf('65', plain,
% 0.68/0.86      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.68/0.86         <= (~
% 0.68/0.86             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.68/0.86      inference('split', [status(esa)], ['34'])).
% 0.68/0.86  thf('66', plain,
% 0.68/0.86      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.68/0.86          != (sk_B)))
% 0.68/0.86         <= (~
% 0.68/0.86             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['64', '65'])).
% 0.68/0.86  thf('67', plain,
% 0.68/0.86      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.68/0.86         <= (~
% 0.68/0.86             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['63', '66'])).
% 0.68/0.86  thf('68', plain,
% 0.68/0.86      ((((sk_B) != (sk_B)))
% 0.68/0.86         <= (~
% 0.68/0.86             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['62', '67'])).
% 0.68/0.86  thf('69', plain,
% 0.68/0.86      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.68/0.86      inference('simplify', [status(thm)], ['68'])).
% 0.68/0.86  thf('70', plain,
% 0.68/0.86      (~
% 0.68/0.86       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.68/0.86       ~
% 0.68/0.86       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.68/0.86      inference('split', [status(esa)], ['34'])).
% 0.68/0.86  thf('71', plain,
% 0.68/0.86      (~
% 0.68/0.86       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.68/0.86          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.68/0.86      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.68/0.86  thf('72', plain,
% 0.68/0.86      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.68/0.86      inference('simpl_trail', [status(thm)], ['42', '71'])).
% 0.68/0.86  thf('73', plain, ($false),
% 0.68/0.86      inference('simplify_reflect-', [status(thm)], ['33', '72'])).
% 0.68/0.86  
% 0.68/0.86  % SZS output end Refutation
% 0.68/0.86  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
