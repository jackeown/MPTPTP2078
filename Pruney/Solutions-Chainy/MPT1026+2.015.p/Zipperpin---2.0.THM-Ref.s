%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oJGuS6fxiE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:54 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  153 (1123 expanded)
%              Number of leaves         :   43 ( 327 expanded)
%              Depth                    :   18
%              Number of atoms          :  989 (12455 expanded)
%              Number of equality atoms :   43 ( 492 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t121_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_funct_2])).

thf('2',plain,(
    r2_hidden @ sk_C_2 @ ( k1_funct_2 @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X56 @ X55 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X56 @ X53 @ X54 ) @ X56 @ X53 @ X54 )
      | ( X55
       != ( k1_funct_2 @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X53: $i,X54: $i,X56: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X56 @ X53 @ X54 ) @ X56 @ X53 @ X54 )
      | ~ ( r2_hidden @ X56 @ ( k1_funct_2 @ X54 @ X53 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_2 @ sk_B_3 @ sk_A ) @ sk_C_2 @ sk_B_3 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_2 @ sk_B_3 @ sk_A ) @ sk_C_2 @ sk_B_3 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X48 = X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_2
    = ( sk_E_1 @ sk_C_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('13',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( ( k1_relat_1 @ X46 )
        = X49 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X39 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('18',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( v1_relat_1 @ X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_3 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_partfun1 @ X40 @ X41 )
      | ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3 )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( v1_funct_1 @ X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3 )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3 )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
   <= ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['29'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['29'])).

thf('38',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3 ) ),
    inference('sat_resolution*',[status(thm)],['33','36','37'])).

thf('39',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3 ) ),
    inference(simpl_trail,[status(thm)],['30','38'])).

thf('40',plain,(
    ~ ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(clc,[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('47',plain,(
    ! [X25: $i] :
      ( ( r1_tarski @ X25 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X25 ) @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('48',plain,
    ( ( r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('50',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('51',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('56',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['50','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','63'])).

thf('65',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('66',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('68',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( v1_partfun1 @ X43 @ X44 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( v1_funct_1 @ X43 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X61: $i] :
      ( ( v1_funct_2 @ X61 @ ( k1_relat_1 @ X61 ) @ ( k2_relat_1 @ X61 ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('73',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('75',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('77',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','77'])).

thf('79',plain,(
    ~ ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(clc,[status(thm)],['28','39'])).

thf('80',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','80'])).

thf('82',plain,(
    ~ ( v1_partfun1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','81'])).

thf('83',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('85',plain,(
    ! [X28: $i,X30: $i,X32: $i,X33: $i] :
      ( ( X30
       != ( k2_relat_1 @ X28 ) )
      | ( r2_hidden @ X32 @ X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X28 ) )
      | ( X32
       != ( k1_funct_1 @ X28 @ X33 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('86',plain,(
    ! [X28: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X33 ) @ ( k2_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_B_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('98',plain,(
    ! [X60: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X60 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('99',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('105',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X59: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X59 ) @ X59 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('107',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['82','96','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oJGuS6fxiE
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.84  % Solved by: fo/fo7.sh
% 0.61/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.84  % done 611 iterations in 0.385s
% 0.61/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.84  % SZS output start Refutation
% 0.61/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.84  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.61/0.84  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.61/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.84  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.61/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.61/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.84  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.61/0.84  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.61/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.84  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.61/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.84  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.61/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.61/0.84  thf(d10_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.84  thf('0', plain,
% 0.61/0.84      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('1', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.61/0.84      inference('simplify', [status(thm)], ['0'])).
% 0.61/0.84  thf(t121_funct_2, conjecture,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.61/0.84       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.61/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.84    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.84        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.61/0.84          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.84            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.61/0.84    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.61/0.84  thf('2', plain, ((r2_hidden @ sk_C_2 @ (k1_funct_2 @ sk_A @ sk_B_3))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(d2_funct_2, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.61/0.84       ( ![D:$i]:
% 0.61/0.84         ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.84           ( ?[E:$i]:
% 0.61/0.84             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.61/0.84               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.61/0.84               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.61/0.84  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.61/0.84  thf(zf_stmt_2, axiom,
% 0.61/0.84    (![E:$i,D:$i,B:$i,A:$i]:
% 0.61/0.84     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.61/0.84       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.61/0.84         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.61/0.84         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.61/0.84  thf(zf_stmt_3, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.61/0.84       ( ![D:$i]:
% 0.61/0.84         ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.84           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.61/0.84  thf('3', plain,
% 0.61/0.84      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X56 @ X55)
% 0.61/0.84          | (zip_tseitin_0 @ (sk_E_1 @ X56 @ X53 @ X54) @ X56 @ X53 @ X54)
% 0.61/0.84          | ((X55) != (k1_funct_2 @ X54 @ X53)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.84  thf('4', plain,
% 0.61/0.84      (![X53 : $i, X54 : $i, X56 : $i]:
% 0.61/0.84         ((zip_tseitin_0 @ (sk_E_1 @ X56 @ X53 @ X54) @ X56 @ X53 @ X54)
% 0.61/0.84          | ~ (r2_hidden @ X56 @ (k1_funct_2 @ X54 @ X53)))),
% 0.61/0.84      inference('simplify', [status(thm)], ['3'])).
% 0.61/0.84  thf('5', plain,
% 0.61/0.84      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_2 @ sk_B_3 @ sk_A) @ sk_C_2 @ sk_B_3 @ 
% 0.61/0.84        sk_A)),
% 0.61/0.84      inference('sup-', [status(thm)], ['2', '4'])).
% 0.61/0.84  thf('6', plain,
% 0.61/0.84      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_2 @ sk_B_3 @ sk_A) @ sk_C_2 @ sk_B_3 @ 
% 0.61/0.84        sk_A)),
% 0.61/0.84      inference('sup-', [status(thm)], ['2', '4'])).
% 0.61/0.84  thf('7', plain,
% 0.61/0.84      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.61/0.84         (((X48) = (X46)) | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.84  thf('8', plain, (((sk_C_2) = (sk_E_1 @ sk_C_2 @ sk_B_3 @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.84  thf('9', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_3 @ sk_A)),
% 0.61/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.61/0.84  thf('10', plain,
% 0.61/0.84      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.61/0.84         ((r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 0.61/0.84          | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.84  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_3)),
% 0.61/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.84  thf('12', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_3 @ sk_A)),
% 0.61/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.61/0.84  thf('13', plain,
% 0.61/0.84      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.61/0.84         (((k1_relat_1 @ X46) = (X49))
% 0.61/0.84          | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.84  thf('14', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.84  thf(t11_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( v1_relat_1 @ C ) =>
% 0.61/0.84       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.61/0.84           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.61/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.61/0.84  thf('15', plain,
% 0.61/0.84      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.61/0.84         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.61/0.84          | ~ (r1_tarski @ (k2_relat_1 @ X37) @ X39)
% 0.61/0.84          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.61/0.84          | ~ (v1_relat_1 @ X37))),
% 0.61/0.84      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.61/0.84  thf('16', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         (~ (r1_tarski @ sk_A @ X0)
% 0.61/0.84          | ~ (v1_relat_1 @ sk_C_2)
% 0.61/0.84          | (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.61/0.84          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['14', '15'])).
% 0.61/0.84  thf('17', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_3 @ sk_A)),
% 0.61/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.61/0.84  thf('18', plain,
% 0.61/0.84      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.61/0.84         ((v1_relat_1 @ X46) | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.84  thf('19', plain, ((v1_relat_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.84  thf('20', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         (~ (r1_tarski @ sk_A @ X0)
% 0.61/0.84          | (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.61/0.84          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X1))),
% 0.61/0.84      inference('demod', [status(thm)], ['16', '19'])).
% 0.61/0.84  thf('21', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_3)))
% 0.61/0.84          | ~ (r1_tarski @ sk_A @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['11', '20'])).
% 0.61/0.84  thf('22', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['1', '21'])).
% 0.61/0.84  thf(cc1_funct_2, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.61/0.84         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.61/0.84  thf('23', plain,
% 0.61/0.84      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.61/0.84         (~ (v1_funct_1 @ X40)
% 0.61/0.84          | ~ (v1_partfun1 @ X40 @ X41)
% 0.61/0.84          | (v1_funct_2 @ X40 @ X41 @ X42)
% 0.61/0.84          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.61/0.84  thf('24', plain,
% 0.61/0.84      (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3)
% 0.61/0.84        | ~ (v1_partfun1 @ sk_C_2 @ sk_A)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C_2))),
% 0.61/0.84      inference('sup-', [status(thm)], ['22', '23'])).
% 0.61/0.84  thf('25', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_3 @ sk_A)),
% 0.61/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.61/0.84  thf('26', plain,
% 0.61/0.84      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.61/0.84         ((v1_funct_1 @ X46) | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.84  thf('27', plain, ((v1_funct_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.84  thf('28', plain,
% 0.61/0.84      (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3) | ~ (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['24', '27'])).
% 0.61/0.84  thf('29', plain,
% 0.61/0.84      ((~ (v1_funct_1 @ sk_C_2)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3)
% 0.61/0.84        | ~ (m1_subset_1 @ sk_C_2 @ 
% 0.61/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('30', plain,
% 0.61/0.84      ((~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3))
% 0.61/0.84         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3)))),
% 0.61/0.84      inference('split', [status(esa)], ['29'])).
% 0.61/0.84  thf('31', plain, ((v1_funct_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.84  thf('32', plain, ((~ (v1_funct_1 @ sk_C_2)) <= (~ ((v1_funct_1 @ sk_C_2)))),
% 0.61/0.84      inference('split', [status(esa)], ['29'])).
% 0.61/0.84  thf('33', plain, (((v1_funct_1 @ sk_C_2))),
% 0.61/0.84      inference('sup-', [status(thm)], ['31', '32'])).
% 0.61/0.84  thf('34', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['1', '21'])).
% 0.61/0.84  thf('35', plain,
% 0.61/0.84      ((~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3))))
% 0.61/0.84         <= (~
% 0.61/0.84             ((m1_subset_1 @ sk_C_2 @ 
% 0.61/0.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))))),
% 0.61/0.84      inference('split', [status(esa)], ['29'])).
% 0.61/0.84  thf('36', plain,
% 0.61/0.84      (((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.84  thf('37', plain,
% 0.61/0.84      (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3)) | 
% 0.61/0.84       ~
% 0.61/0.84       ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))) | 
% 0.61/0.84       ~ ((v1_funct_1 @ sk_C_2))),
% 0.61/0.84      inference('split', [status(esa)], ['29'])).
% 0.61/0.84  thf('38', plain, (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3))),
% 0.61/0.84      inference('sat_resolution*', [status(thm)], ['33', '36', '37'])).
% 0.61/0.84  thf('39', plain, (~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_3)),
% 0.61/0.84      inference('simpl_trail', [status(thm)], ['30', '38'])).
% 0.61/0.84  thf('40', plain, (~ (v1_partfun1 @ sk_C_2 @ sk_A)),
% 0.61/0.84      inference('clc', [status(thm)], ['28', '39'])).
% 0.61/0.84  thf('41', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.61/0.84      inference('simplify', [status(thm)], ['0'])).
% 0.61/0.84  thf(t3_subset, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.84  thf('42', plain,
% 0.61/0.84      (![X19 : $i, X21 : $i]:
% 0.61/0.84         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.61/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.84  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['41', '42'])).
% 0.61/0.84  thf(cc4_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( v1_xboole_0 @ A ) =>
% 0.61/0.84       ( ![C:$i]:
% 0.61/0.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.61/0.84           ( v1_xboole_0 @ C ) ) ) ))).
% 0.61/0.84  thf('44', plain,
% 0.61/0.84      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.61/0.84         (~ (v1_xboole_0 @ X34)
% 0.61/0.84          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.61/0.84          | (v1_xboole_0 @ X35))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.61/0.84  thf('45', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.61/0.84  thf('46', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.84  thf(t21_relat_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( v1_relat_1 @ A ) =>
% 0.61/0.84       ( r1_tarski @
% 0.61/0.84         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.61/0.84  thf('47', plain,
% 0.61/0.84      (![X25 : $i]:
% 0.61/0.84         ((r1_tarski @ X25 @ 
% 0.61/0.84           (k2_zfmisc_1 @ (k1_relat_1 @ X25) @ (k2_relat_1 @ X25)))
% 0.61/0.84          | ~ (v1_relat_1 @ X25))),
% 0.61/0.84      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.61/0.84  thf('48', plain,
% 0.61/0.84      (((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2)))
% 0.61/0.84        | ~ (v1_relat_1 @ sk_C_2))),
% 0.61/0.84      inference('sup+', [status(thm)], ['46', '47'])).
% 0.61/0.84  thf('49', plain, ((v1_relat_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.84  thf('50', plain,
% 0.61/0.84      ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.84      inference('demod', [status(thm)], ['48', '49'])).
% 0.61/0.84  thf(t7_xboole_0, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.61/0.84          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.61/0.84  thf('51', plain,
% 0.61/0.84      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.61/0.84      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.61/0.84  thf(d1_xboole_0, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.61/0.84  thf('52', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.84  thf('53', plain,
% 0.61/0.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.61/0.84  thf(d3_tarski, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.84  thf('54', plain,
% 0.61/0.84      (![X4 : $i, X6 : $i]:
% 0.61/0.84         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf(t113_zfmisc_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.61/0.84       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.61/0.84  thf('55', plain,
% 0.61/0.84      (![X12 : $i, X13 : $i]:
% 0.61/0.84         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.61/0.84          | ((X13) != (k1_xboole_0)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.61/0.84  thf('56', plain,
% 0.61/0.84      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.84      inference('simplify', [status(thm)], ['55'])).
% 0.61/0.84  thf(t152_zfmisc_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.61/0.84  thf('57', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]: ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.61/0.84      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.61/0.84  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.61/0.84      inference('sup-', [status(thm)], ['56', '57'])).
% 0.61/0.84  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.84      inference('sup-', [status(thm)], ['54', '58'])).
% 0.61/0.84  thf('60', plain,
% 0.61/0.84      (![X8 : $i, X10 : $i]:
% 0.61/0.84         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('61', plain,
% 0.61/0.84      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.61/0.84  thf('62', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         (~ (r1_tarski @ X1 @ X0)
% 0.61/0.84          | ~ (v1_xboole_0 @ X0)
% 0.61/0.84          | ((X1) = (k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['53', '61'])).
% 0.61/0.84  thf('63', plain,
% 0.61/0.84      ((((sk_C_2) = (k1_xboole_0))
% 0.61/0.84        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['50', '62'])).
% 0.61/0.84  thf('64', plain,
% 0.61/0.84      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['45', '63'])).
% 0.61/0.84  thf('65', plain,
% 0.61/0.84      ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.84      inference('demod', [status(thm)], ['48', '49'])).
% 0.61/0.84  thf('66', plain,
% 0.61/0.84      (![X19 : $i, X21 : $i]:
% 0.61/0.84         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.61/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.84  thf('67', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C_2 @ 
% 0.61/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['65', '66'])).
% 0.61/0.84  thf(cc5_funct_2, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.61/0.84       ( ![C:$i]:
% 0.61/0.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.61/0.84             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.61/0.84  thf('68', plain,
% 0.61/0.84      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.61/0.84         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.61/0.84          | (v1_partfun1 @ X43 @ X44)
% 0.61/0.84          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.61/0.84          | ~ (v1_funct_1 @ X43)
% 0.61/0.84          | (v1_xboole_0 @ X45))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.61/0.84  thf('69', plain,
% 0.61/0.84      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C_2)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))
% 0.61/0.84        | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['67', '68'])).
% 0.61/0.84  thf('70', plain, ((v1_funct_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.84  thf('71', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.84  thf(t3_funct_2, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.84       ( ( v1_funct_1 @ A ) & 
% 0.61/0.84         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.61/0.84         ( m1_subset_1 @
% 0.61/0.84           A @ 
% 0.61/0.84           ( k1_zfmisc_1 @
% 0.61/0.84             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.61/0.84  thf('72', plain,
% 0.61/0.84      (![X61 : $i]:
% 0.61/0.84         ((v1_funct_2 @ X61 @ (k1_relat_1 @ X61) @ (k2_relat_1 @ X61))
% 0.61/0.84          | ~ (v1_funct_1 @ X61)
% 0.61/0.84          | ~ (v1_relat_1 @ X61))),
% 0.61/0.84      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.61/0.84  thf('73', plain,
% 0.61/0.84      (((v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))
% 0.61/0.84        | ~ (v1_relat_1 @ sk_C_2)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C_2))),
% 0.61/0.84      inference('sup+', [status(thm)], ['71', '72'])).
% 0.61/0.84  thf('74', plain, ((v1_funct_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.84  thf('75', plain,
% 0.61/0.84      (((v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))
% 0.61/0.84        | ~ (v1_relat_1 @ sk_C_2))),
% 0.61/0.84      inference('demod', [status(thm)], ['73', '74'])).
% 0.61/0.84  thf('76', plain, ((v1_relat_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.84  thf('77', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))),
% 0.61/0.84      inference('demod', [status(thm)], ['75', '76'])).
% 0.61/0.84  thf('78', plain,
% 0.61/0.84      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['69', '70', '77'])).
% 0.61/0.84  thf('79', plain, (~ (v1_partfun1 @ sk_C_2 @ sk_A)),
% 0.61/0.84      inference('clc', [status(thm)], ['28', '39'])).
% 0.61/0.84  thf('80', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 0.61/0.84      inference('sup-', [status(thm)], ['78', '79'])).
% 0.61/0.84  thf('81', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['64', '80'])).
% 0.61/0.84  thf('82', plain, (~ (v1_partfun1 @ k1_xboole_0 @ sk_A)),
% 0.61/0.84      inference('demod', [status(thm)], ['40', '81'])).
% 0.61/0.84  thf('83', plain,
% 0.61/0.84      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.61/0.84      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.61/0.84  thf('84', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.84  thf(d5_funct_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( r2_hidden @ C @ B ) <=>
% 0.61/0.84               ( ?[D:$i]:
% 0.61/0.84                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.61/0.84                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf('85', plain,
% 0.61/0.84      (![X28 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 0.61/0.84         (((X30) != (k2_relat_1 @ X28))
% 0.61/0.84          | (r2_hidden @ X32 @ X30)
% 0.61/0.84          | ~ (r2_hidden @ X33 @ (k1_relat_1 @ X28))
% 0.61/0.84          | ((X32) != (k1_funct_1 @ X28 @ X33))
% 0.61/0.84          | ~ (v1_funct_1 @ X28)
% 0.61/0.84          | ~ (v1_relat_1 @ X28))),
% 0.61/0.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.61/0.84  thf('86', plain,
% 0.61/0.84      (![X28 : $i, X33 : $i]:
% 0.61/0.84         (~ (v1_relat_1 @ X28)
% 0.61/0.84          | ~ (v1_funct_1 @ X28)
% 0.61/0.84          | ~ (r2_hidden @ X33 @ (k1_relat_1 @ X28))
% 0.61/0.84          | (r2_hidden @ (k1_funct_1 @ X28 @ X33) @ (k2_relat_1 @ X28)))),
% 0.61/0.84      inference('simplify', [status(thm)], ['85'])).
% 0.61/0.84  thf('87', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.84          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.61/0.84          | ~ (v1_funct_1 @ sk_C_2)
% 0.61/0.84          | ~ (v1_relat_1 @ sk_C_2))),
% 0.61/0.84      inference('sup-', [status(thm)], ['84', '86'])).
% 0.61/0.84  thf('88', plain, ((v1_funct_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.84  thf('89', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.84          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.61/0.84          | ~ (v1_relat_1 @ sk_C_2))),
% 0.61/0.84      inference('demod', [status(thm)], ['87', '88'])).
% 0.61/0.84  thf('90', plain, ((v1_relat_1 @ sk_C_2)),
% 0.61/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.84  thf('91', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.84          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.84      inference('demod', [status(thm)], ['89', '90'])).
% 0.61/0.84  thf('92', plain,
% 0.61/0.84      ((((sk_A) = (k1_xboole_0))
% 0.61/0.84        | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_B_1 @ sk_A)) @ 
% 0.61/0.84           (k2_relat_1 @ sk_C_2)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['83', '91'])).
% 0.61/0.84  thf('93', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.84  thf('94', plain,
% 0.61/0.84      ((((sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['92', '93'])).
% 0.61/0.84  thf('95', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 0.61/0.84      inference('sup-', [status(thm)], ['78', '79'])).
% 0.61/0.84  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['94', '95'])).
% 0.61/0.84  thf('97', plain,
% 0.61/0.84      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.84      inference('simplify', [status(thm)], ['55'])).
% 0.61/0.84  thf(dt_k6_partfun1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( m1_subset_1 @
% 0.61/0.84         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.61/0.84       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.61/0.84  thf('98', plain,
% 0.61/0.84      (![X60 : $i]:
% 0.61/0.84         (m1_subset_1 @ (k6_partfun1 @ X60) @ 
% 0.61/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X60)))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.61/0.84  thf('99', plain,
% 0.61/0.84      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['97', '98'])).
% 0.61/0.84  thf('100', plain,
% 0.61/0.84      (![X19 : $i, X20 : $i]:
% 0.61/0.84         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.84  thf('101', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.61/0.84      inference('sup-', [status(thm)], ['99', '100'])).
% 0.61/0.84  thf('102', plain,
% 0.61/0.84      (![X8 : $i, X10 : $i]:
% 0.61/0.84         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('103', plain,
% 0.61/0.84      ((~ (r1_tarski @ k1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))
% 0.61/0.84        | ((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['101', '102'])).
% 0.61/0.84  thf('104', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.84      inference('sup-', [status(thm)], ['54', '58'])).
% 0.61/0.84  thf('105', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['103', '104'])).
% 0.61/0.84  thf('106', plain, (![X59 : $i]: (v1_partfun1 @ (k6_partfun1 @ X59) @ X59)),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.61/0.84  thf('107', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.61/0.84      inference('sup+', [status(thm)], ['105', '106'])).
% 0.61/0.84  thf('108', plain, ($false),
% 0.61/0.84      inference('demod', [status(thm)], ['82', '96', '107'])).
% 0.61/0.84  
% 0.61/0.84  % SZS output end Refutation
% 0.61/0.84  
% 0.61/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
