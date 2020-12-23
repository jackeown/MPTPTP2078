%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m2j5IlLqVp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:53 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 670 expanded)
%              Number of leaves         :   35 ( 200 expanded)
%              Depth                    :   16
%              Number of atoms          :  801 (7497 expanded)
%              Number of equality atoms :   21 ( 281 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('1',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) ),
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

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X42 @ X39 @ X40 ) @ X42 @ X39 @ X40 )
      | ( X41
       != ( k1_funct_2 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X39: $i,X40: $i,X42: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X42 @ X39 @ X40 ) @ X42 @ X39 @ X40 )
      | ~ ( r2_hidden @ X42 @ ( k1_funct_2 @ X40 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['1','3'])).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,
    ( sk_C_1
    = ( sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ X32 )
        = X35 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X16
       != ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X14 ) )
      | ( X18
       != ( k1_funct_1 @ X14 @ X19 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('12',plain,(
    ! [X14: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X19 ) @ ( k2_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_funct_1 @ X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['13','16','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( v1_partfun1 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X33 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_partfun1 @ X23 @ X24 )
      | ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('45',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('47',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['48'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['48'])).

thf('57',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['52','55','56'])).

thf('58',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['49','57'])).

thf('59',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['47','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','59'])).

thf('61',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['21','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X45: $i] :
      ( ( v1_funct_2 @ X45 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['64','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('73',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('75',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['47','58'])).

thf('77',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['63','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m2j5IlLqVp
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 138 iterations in 0.098s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(d1_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf(t121_funct_2, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.38/0.56       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.56        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.38/0.56          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.38/0.56  thf('1', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d2_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56           ( ?[E:$i]:
% 0.38/0.56             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.38/0.56               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.38/0.56               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_2, axiom,
% 0.38/0.56    (![E:$i,D:$i,B:$i,A:$i]:
% 0.38/0.56     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.38/0.56       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.38/0.56         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.38/0.56         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.38/0.56  thf(zf_stmt_3, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X42 @ X41)
% 0.38/0.56          | (zip_tseitin_0 @ (sk_E_1 @ X42 @ X39 @ X40) @ X42 @ X39 @ X40)
% 0.38/0.56          | ((X41) != (k1_funct_2 @ X40 @ X39)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X39 : $i, X40 : $i, X42 : $i]:
% 0.38/0.56         ((zip_tseitin_0 @ (sk_E_1 @ X42 @ X39 @ X40) @ X42 @ X39 @ X40)
% 0.38/0.56          | ~ (r2_hidden @ X42 @ (k1_funct_2 @ X40 @ X39)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_C_1 @ sk_B_2 @ 
% 0.38/0.56        sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '3'])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_C_1 @ sk_B_2 @ 
% 0.38/0.56        sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '3'])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         (((X34) = (X32)) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.56  thf('7', plain, (((sk_C_1) = (sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('8', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         (((k1_relat_1 @ X32) = (X35))
% 0.38/0.56          | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.56  thf('10', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf(d5_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.56               ( ?[D:$i]:
% 0.38/0.56                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.38/0.56                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.38/0.56         (((X16) != (k2_relat_1 @ X14))
% 0.38/0.56          | (r2_hidden @ X18 @ X16)
% 0.38/0.56          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X14))
% 0.38/0.56          | ((X18) != (k1_funct_1 @ X14 @ X19))
% 0.38/0.56          | ~ (v1_funct_1 @ X14)
% 0.38/0.56          | ~ (v1_relat_1 @ X14))),
% 0.38/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X14 : $i, X19 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X14)
% 0.38/0.56          | ~ (v1_funct_1 @ X14)
% 0.38/0.56          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X14))
% 0.38/0.56          | (r2_hidden @ (k1_funct_1 @ X14 @ X19) @ (k2_relat_1 @ X14)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.56          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.38/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.56          | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '12'])).
% 0.38/0.56  thf('14', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         ((v1_funct_1 @ X32) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.56  thf('16', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('17', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         ((v1_relat_1 @ X32) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.56  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.56          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['13', '16', '19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_A)
% 0.38/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_B @ sk_A)) @ 
% 0.38/0.56           (k2_relat_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '20'])).
% 0.38/0.56  thf('22', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf(t21_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( r1_tarski @
% 0.38/0.56         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X12 : $i]:
% 0.38/0.56         ((r1_tarski @ X12 @ 
% 0.38/0.56           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.38/0.56          | ~ (v1_relat_1 @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.38/0.56  thf(t3_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X9 : $i, X11 : $i]:
% 0.38/0.56         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | (m1_subset_1 @ X0 @ 
% 0.38/0.56             (k1_zfmisc_1 @ 
% 0.38/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf(cc1_partfun1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.56         (~ (v1_xboole_0 @ X26)
% 0.38/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 0.38/0.56          | (v1_partfun1 @ X27 @ X26))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      ((~ (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_partfun1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 0.38/0.56        | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['22', '27'])).
% 0.38/0.56  thf('29', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      ((~ (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.56  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('32', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.56  thf('33', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         ((r1_tarski @ (k2_relat_1 @ X32) @ X33)
% 0.38/0.56          | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.56  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2)),
% 0.38/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.56  thf(d10_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.56  thf('37', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.38/0.56      inference('simplify', [status(thm)], ['36'])).
% 0.38/0.56  thf(t11_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ C ) =>
% 0.38/0.56       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.38/0.56           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.38/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.56         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.38/0.56          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.38/0.56          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.38/0.56          | ~ (v1_relat_1 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | (m1_subset_1 @ X0 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.38/0.56          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_2)))
% 0.38/0.56        | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['35', '39'])).
% 0.38/0.56  thf('41', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.38/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.38/0.56  thf(cc1_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.38/0.56         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.56         (~ (v1_funct_1 @ X23)
% 0.38/0.56          | ~ (v1_partfun1 @ X23 @ X24)
% 0.38/0.56          | (v1_funct_2 @ X23 @ X24 @ X25)
% 0.38/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.38/0.56        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('46', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2) | ~ (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_C_1)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.38/0.56        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))
% 0.38/0.56         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)))),
% 0.38/0.56      inference('split', [status(esa)], ['48'])).
% 0.38/0.56  thf('50', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('51', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['48'])).
% 0.38/0.56  thf('52', plain, (((v1_funct_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.38/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.38/0.56  thf('54', plain,
% 0.38/0.56      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))
% 0.38/0.56         <= (~
% 0.38/0.56             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))))),
% 0.38/0.56      inference('split', [status(esa)], ['48'])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)) | 
% 0.38/0.56       ~
% 0.38/0.56       ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))) | 
% 0.38/0.56       ~ ((v1_funct_1 @ sk_C_1))),
% 0.38/0.56      inference('split', [status(esa)], ['48'])).
% 0.38/0.56  thf('57', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['52', '55', '56'])).
% 0.38/0.56  thf('58', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['49', '57'])).
% 0.38/0.56  thf('59', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['47', '58'])).
% 0.38/0.56  thf('60', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['32', '59'])).
% 0.38/0.56  thf('61', plain,
% 0.38/0.56      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_B @ sk_A)) @ 
% 0.38/0.56        (k2_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('clc', [status(thm)], ['21', '60'])).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('63', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.56  thf('64', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf(t3_funct_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ( v1_funct_1 @ A ) & 
% 0.38/0.56         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.38/0.56         ( m1_subset_1 @
% 0.38/0.56           A @ 
% 0.38/0.56           ( k1_zfmisc_1 @
% 0.38/0.56             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('65', plain,
% 0.38/0.56      (![X45 : $i]:
% 0.38/0.56         ((v1_funct_2 @ X45 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))
% 0.38/0.56          | ~ (v1_funct_1 @ X45)
% 0.38/0.56          | ~ (v1_relat_1 @ X45))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.38/0.56  thf('66', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | (m1_subset_1 @ X0 @ 
% 0.38/0.56             (k1_zfmisc_1 @ 
% 0.38/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf(cc5_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.38/0.56             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('67', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.38/0.56          | (v1_partfun1 @ X29 @ X30)
% 0.38/0.56          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.38/0.56          | ~ (v1_funct_1 @ X29)
% 0.38/0.56          | (v1_xboole_0 @ X31))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.38/0.56          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['65', '68'])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.38/0.56          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['69'])).
% 0.38/0.56  thf('71', plain,
% 0.38/0.56      (((v1_partfun1 @ sk_C_1 @ sk_A)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.56        | (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['64', '70'])).
% 0.38/0.56  thf('72', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      (((v1_partfun1 @ sk_C_1 @ sk_A)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.56        | (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.38/0.56  thf('74', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (((v1_partfun1 @ sk_C_1 @ sk_A) | (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.56  thf('76', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['47', '58'])).
% 0.38/0.56  thf('77', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('clc', [status(thm)], ['75', '76'])).
% 0.38/0.56  thf('78', plain, ($false), inference('demod', [status(thm)], ['63', '77'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
