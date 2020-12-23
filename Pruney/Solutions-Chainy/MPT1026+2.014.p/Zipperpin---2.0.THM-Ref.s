%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tGb2aC4FDh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:54 EST 2020

% Result     : Theorem 2.98s
% Output     : Refutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  146 (1482 expanded)
%              Number of leaves         :   46 ( 432 expanded)
%              Depth                    :   20
%              Number of atoms          :  943 (16793 expanded)
%              Number of equality atoms :   39 ( 647 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X42 @ X39 @ X40 ) @ X42 @ X39 @ X40 )
      | ( X41
       != ( k1_funct_2 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X39: $i,X40: $i,X42: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X42 @ X39 @ X40 ) @ X42 @ X39 @ X40 )
      | ~ ( r2_hidden @ X42 @ ( k1_funct_2 @ X40 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C
    = ( sk_E_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_funct_1 @ X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ sk_C @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X33 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    zip_tseitin_0 @ sk_C @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ X32 )
        = X35 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['13','30','31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X45: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('49',plain,(
    ! [X45: $i] :
      ( ( v1_funct_2 @ X45 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('50',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','53'])).

thf('55',plain,(
    ! [X45: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_partfun1 @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('61',plain,
    ( ( v1_partfun1 @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('63',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_partfun1 @ X26 @ X27 )
      | ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('64',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('66',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('68',plain,(
    ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','69'])).

thf('71',plain,(
    ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','70'])).

thf('72',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['61','68'])).

thf('73',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('77',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( zip_tseitin_1 @ X46 @ X47 @ X48 @ X49 )
      | ( r2_hidden @ X46 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k1_relat_1 @ X54 )
       != X53 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X54 @ X55 @ X53 ) @ X54 @ X55 @ X53 )
      | ( zip_tseitin_2 @ X54 @ X55 @ X53 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('79',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ~ ( v1_funct_1 @ X54 )
      | ( zip_tseitin_2 @ X54 @ X55 @ ( k1_relat_1 @ X54 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X54 @ X55 @ ( k1_relat_1 @ X54 ) ) @ X54 @ X55 @ ( k1_relat_1 @ X54 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['76','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('88',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('89',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82','86','89','90'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( zip_tseitin_2 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['75','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tGb2aC4FDh
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.98/3.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.98/3.19  % Solved by: fo/fo7.sh
% 2.98/3.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.98/3.19  % done 4190 iterations in 2.766s
% 2.98/3.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.98/3.19  % SZS output start Refutation
% 2.98/3.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.98/3.19  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.98/3.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.98/3.19  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 2.98/3.19  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.98/3.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.98/3.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.98/3.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.98/3.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.98/3.19  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 2.98/3.19  thf(sk_A_type, type, sk_A: $i).
% 2.98/3.19  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 2.98/3.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.98/3.19  thf(sk_C_type, type, sk_C: $i).
% 2.98/3.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.98/3.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.98/3.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.98/3.19  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.98/3.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 2.98/3.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.98/3.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.98/3.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.98/3.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.98/3.19  thf(t121_funct_2, conjecture,
% 2.98/3.19    (![A:$i,B:$i,C:$i]:
% 2.98/3.19     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 2.98/3.19       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.98/3.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.98/3.19  thf(zf_stmt_0, negated_conjecture,
% 2.98/3.19    (~( ![A:$i,B:$i,C:$i]:
% 2.98/3.19        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 2.98/3.19          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.98/3.19            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 2.98/3.19    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 2.98/3.19  thf('0', plain,
% 2.98/3.19      ((~ (v1_funct_1 @ sk_C)
% 2.98/3.19        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 2.98/3.19        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.19  thf('1', plain,
% 2.98/3.19      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))
% 2.98/3.19         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)))),
% 2.98/3.19      inference('split', [status(esa)], ['0'])).
% 2.98/3.19  thf('2', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.19  thf(d2_funct_2, axiom,
% 2.98/3.19    (![A:$i,B:$i,C:$i]:
% 2.98/3.19     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 2.98/3.19       ( ![D:$i]:
% 2.98/3.19         ( ( r2_hidden @ D @ C ) <=>
% 2.98/3.19           ( ?[E:$i]:
% 2.98/3.19             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 2.98/3.19               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 2.98/3.19               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 2.98/3.19  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.98/3.19  thf(zf_stmt_2, axiom,
% 2.98/3.19    (![E:$i,D:$i,B:$i,A:$i]:
% 2.98/3.19     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 2.98/3.19       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 2.98/3.19         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 2.98/3.19         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 2.98/3.19  thf(zf_stmt_3, axiom,
% 2.98/3.19    (![A:$i,B:$i,C:$i]:
% 2.98/3.19     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 2.98/3.19       ( ![D:$i]:
% 2.98/3.19         ( ( r2_hidden @ D @ C ) <=>
% 2.98/3.19           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 2.98/3.19  thf('3', plain,
% 2.98/3.19      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.98/3.19         (~ (r2_hidden @ X42 @ X41)
% 2.98/3.19          | (zip_tseitin_0 @ (sk_E_1 @ X42 @ X39 @ X40) @ X42 @ X39 @ X40)
% 2.98/3.19          | ((X41) != (k1_funct_2 @ X40 @ X39)))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.98/3.19  thf('4', plain,
% 2.98/3.19      (![X39 : $i, X40 : $i, X42 : $i]:
% 2.98/3.19         ((zip_tseitin_0 @ (sk_E_1 @ X42 @ X39 @ X40) @ X42 @ X39 @ X40)
% 2.98/3.19          | ~ (r2_hidden @ X42 @ (k1_funct_2 @ X40 @ X39)))),
% 2.98/3.19      inference('simplify', [status(thm)], ['3'])).
% 2.98/3.19  thf('5', plain,
% 2.98/3.19      ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_B_1 @ sk_A) @ sk_C @ sk_B_1 @ sk_A)),
% 2.98/3.19      inference('sup-', [status(thm)], ['2', '4'])).
% 2.98/3.19  thf('6', plain,
% 2.98/3.19      ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_B_1 @ sk_A) @ sk_C @ sk_B_1 @ sk_A)),
% 2.98/3.19      inference('sup-', [status(thm)], ['2', '4'])).
% 2.98/3.19  thf('7', plain,
% 2.98/3.19      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.98/3.19         (((X34) = (X32)) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.98/3.19  thf('8', plain, (((sk_C) = (sk_E_1 @ sk_C @ sk_B_1 @ sk_A))),
% 2.98/3.19      inference('sup-', [status(thm)], ['6', '7'])).
% 2.98/3.19  thf('9', plain, ((zip_tseitin_0 @ sk_C @ sk_C @ sk_B_1 @ sk_A)),
% 2.98/3.19      inference('demod', [status(thm)], ['5', '8'])).
% 2.98/3.19  thf('10', plain,
% 2.98/3.19      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.98/3.19         ((v1_funct_1 @ X32) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.98/3.19  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['9', '10'])).
% 2.98/3.19  thf('12', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 2.98/3.19      inference('split', [status(esa)], ['0'])).
% 2.98/3.19  thf('13', plain, (((v1_funct_1 @ sk_C))),
% 2.98/3.19      inference('sup-', [status(thm)], ['11', '12'])).
% 2.98/3.19  thf('14', plain, ((zip_tseitin_0 @ sk_C @ sk_C @ sk_B_1 @ sk_A)),
% 2.98/3.19      inference('demod', [status(thm)], ['5', '8'])).
% 2.98/3.19  thf('15', plain,
% 2.98/3.19      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.98/3.19         ((r1_tarski @ (k2_relat_1 @ X32) @ X33)
% 2.98/3.19          | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.98/3.19  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 2.98/3.19      inference('sup-', [status(thm)], ['14', '15'])).
% 2.98/3.19  thf(d10_xboole_0, axiom,
% 2.98/3.19    (![A:$i,B:$i]:
% 2.98/3.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.98/3.19  thf('17', plain,
% 2.98/3.19      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.98/3.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.98/3.19  thf('18', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.98/3.19      inference('simplify', [status(thm)], ['17'])).
% 2.98/3.19  thf(t11_relset_1, axiom,
% 2.98/3.19    (![A:$i,B:$i,C:$i]:
% 2.98/3.19     ( ( v1_relat_1 @ C ) =>
% 2.98/3.19       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 2.98/3.19           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 2.98/3.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.98/3.19  thf('19', plain,
% 2.98/3.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.98/3.19         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 2.98/3.19          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 2.98/3.19          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.98/3.19          | ~ (v1_relat_1 @ X23))),
% 2.98/3.19      inference('cnf', [status(esa)], [t11_relset_1])).
% 2.98/3.19  thf('20', plain,
% 2.98/3.19      (![X0 : $i, X1 : $i]:
% 2.98/3.19         (~ (v1_relat_1 @ X0)
% 2.98/3.19          | (m1_subset_1 @ X0 @ 
% 2.98/3.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 2.98/3.19          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 2.98/3.19      inference('sup-', [status(thm)], ['18', '19'])).
% 2.98/3.19  thf('21', plain,
% 2.98/3.19      (((m1_subset_1 @ sk_C @ 
% 2.98/3.19         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)))
% 2.98/3.19        | ~ (v1_relat_1 @ sk_C))),
% 2.98/3.19      inference('sup-', [status(thm)], ['16', '20'])).
% 2.98/3.19  thf('22', plain, ((zip_tseitin_0 @ sk_C @ sk_C @ sk_B_1 @ sk_A)),
% 2.98/3.19      inference('demod', [status(thm)], ['5', '8'])).
% 2.98/3.19  thf('23', plain,
% 2.98/3.19      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.98/3.19         (((k1_relat_1 @ X32) = (X35))
% 2.98/3.19          | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.98/3.19  thf('24', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 2.98/3.19      inference('sup-', [status(thm)], ['22', '23'])).
% 2.98/3.19  thf('25', plain, ((zip_tseitin_0 @ sk_C @ sk_C @ sk_B_1 @ sk_A)),
% 2.98/3.19      inference('demod', [status(thm)], ['5', '8'])).
% 2.98/3.19  thf('26', plain,
% 2.98/3.19      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.98/3.19         ((v1_relat_1 @ X32) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.98/3.19  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['25', '26'])).
% 2.98/3.19  thf('28', plain,
% 2.98/3.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.98/3.19      inference('demod', [status(thm)], ['21', '24', '27'])).
% 2.98/3.19  thf('29', plain,
% 2.98/3.19      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 2.98/3.19         <= (~
% 2.98/3.19             ((m1_subset_1 @ sk_C @ 
% 2.98/3.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))),
% 2.98/3.19      inference('split', [status(esa)], ['0'])).
% 2.98/3.19  thf('30', plain,
% 2.98/3.19      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 2.98/3.19      inference('sup-', [status(thm)], ['28', '29'])).
% 2.98/3.19  thf('31', plain,
% 2.98/3.19      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)) | 
% 2.98/3.19       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))) | 
% 2.98/3.19       ~ ((v1_funct_1 @ sk_C))),
% 2.98/3.19      inference('split', [status(esa)], ['0'])).
% 2.98/3.19  thf('32', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 2.98/3.19      inference('sat_resolution*', [status(thm)], ['13', '30', '31'])).
% 2.98/3.19  thf('33', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.98/3.19      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 2.98/3.19  thf('34', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 2.98/3.19      inference('sup-', [status(thm)], ['22', '23'])).
% 2.98/3.19  thf(l13_xboole_0, axiom,
% 2.98/3.19    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.98/3.19  thf('35', plain,
% 2.98/3.19      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 2.98/3.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.98/3.19  thf(t60_relat_1, axiom,
% 2.98/3.19    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.98/3.19     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.98/3.19  thf('36', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.98/3.19      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.98/3.19  thf('37', plain,
% 2.98/3.19      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.98/3.19      inference('sup+', [status(thm)], ['35', '36'])).
% 2.98/3.19  thf('38', plain, ((((sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 2.98/3.19      inference('sup+', [status(thm)], ['34', '37'])).
% 2.98/3.19  thf('39', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 2.98/3.19      inference('sup-', [status(thm)], ['22', '23'])).
% 2.98/3.19  thf(t3_funct_2, axiom,
% 2.98/3.19    (![A:$i]:
% 2.98/3.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.98/3.19       ( ( v1_funct_1 @ A ) & 
% 2.98/3.19         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.98/3.19         ( m1_subset_1 @
% 2.98/3.19           A @ 
% 2.98/3.19           ( k1_zfmisc_1 @
% 2.98/3.19             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.98/3.19  thf('40', plain,
% 2.98/3.19      (![X45 : $i]:
% 2.98/3.19         ((m1_subset_1 @ X45 @ 
% 2.98/3.19           (k1_zfmisc_1 @ 
% 2.98/3.19            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 2.98/3.19          | ~ (v1_funct_1 @ X45)
% 2.98/3.19          | ~ (v1_relat_1 @ X45))),
% 2.98/3.19      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.98/3.19  thf('41', plain,
% 2.98/3.19      (((m1_subset_1 @ sk_C @ 
% 2.98/3.19         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))
% 2.98/3.19        | ~ (v1_relat_1 @ sk_C)
% 2.98/3.19        | ~ (v1_funct_1 @ sk_C))),
% 2.98/3.19      inference('sup+', [status(thm)], ['39', '40'])).
% 2.98/3.19  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['25', '26'])).
% 2.98/3.19  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['9', '10'])).
% 2.98/3.19  thf('44', plain,
% 2.98/3.19      ((m1_subset_1 @ sk_C @ 
% 2.98/3.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 2.98/3.19      inference('demod', [status(thm)], ['41', '42', '43'])).
% 2.98/3.19  thf(cc5_funct_2, axiom,
% 2.98/3.19    (![A:$i,B:$i]:
% 2.98/3.19     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.98/3.19       ( ![C:$i]:
% 2.98/3.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.98/3.19           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 2.98/3.19             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 2.98/3.19  thf('45', plain,
% 2.98/3.19      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.98/3.19         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.98/3.19          | (v1_partfun1 @ X29 @ X30)
% 2.98/3.19          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 2.98/3.19          | ~ (v1_funct_1 @ X29)
% 2.98/3.19          | (v1_xboole_0 @ X31))),
% 2.98/3.19      inference('cnf', [status(esa)], [cc5_funct_2])).
% 2.98/3.19  thf('46', plain,
% 2.98/3.19      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.98/3.19        | ~ (v1_funct_1 @ sk_C)
% 2.98/3.19        | ~ (v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))
% 2.98/3.19        | (v1_partfun1 @ sk_C @ sk_A))),
% 2.98/3.19      inference('sup-', [status(thm)], ['44', '45'])).
% 2.98/3.19  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['9', '10'])).
% 2.98/3.19  thf('48', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 2.98/3.19      inference('sup-', [status(thm)], ['22', '23'])).
% 2.98/3.19  thf('49', plain,
% 2.98/3.19      (![X45 : $i]:
% 2.98/3.19         ((v1_funct_2 @ X45 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))
% 2.98/3.19          | ~ (v1_funct_1 @ X45)
% 2.98/3.19          | ~ (v1_relat_1 @ X45))),
% 2.98/3.19      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.98/3.19  thf('50', plain,
% 2.98/3.19      (((v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))
% 2.98/3.19        | ~ (v1_relat_1 @ sk_C)
% 2.98/3.19        | ~ (v1_funct_1 @ sk_C))),
% 2.98/3.19      inference('sup+', [status(thm)], ['48', '49'])).
% 2.98/3.19  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['25', '26'])).
% 2.98/3.19  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['9', '10'])).
% 2.98/3.19  thf('53', plain, ((v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))),
% 2.98/3.19      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.98/3.19  thf('54', plain,
% 2.98/3.19      (((v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v1_partfun1 @ sk_C @ sk_A))),
% 2.98/3.19      inference('demod', [status(thm)], ['46', '47', '53'])).
% 2.98/3.19  thf('55', plain,
% 2.98/3.19      (![X45 : $i]:
% 2.98/3.19         ((m1_subset_1 @ X45 @ 
% 2.98/3.19           (k1_zfmisc_1 @ 
% 2.98/3.19            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 2.98/3.19          | ~ (v1_funct_1 @ X45)
% 2.98/3.19          | ~ (v1_relat_1 @ X45))),
% 2.98/3.19      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.98/3.19  thf(cc4_relset_1, axiom,
% 2.98/3.19    (![A:$i,B:$i]:
% 2.98/3.19     ( ( v1_xboole_0 @ A ) =>
% 2.98/3.19       ( ![C:$i]:
% 2.98/3.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.98/3.19           ( v1_xboole_0 @ C ) ) ) ))).
% 2.98/3.19  thf('56', plain,
% 2.98/3.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.98/3.19         (~ (v1_xboole_0 @ X20)
% 2.98/3.19          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 2.98/3.19          | (v1_xboole_0 @ X21))),
% 2.98/3.19      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.98/3.19  thf('57', plain,
% 2.98/3.19      (![X0 : $i]:
% 2.98/3.19         (~ (v1_relat_1 @ X0)
% 2.98/3.19          | ~ (v1_funct_1 @ X0)
% 2.98/3.19          | (v1_xboole_0 @ X0)
% 2.98/3.19          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 2.98/3.19      inference('sup-', [status(thm)], ['55', '56'])).
% 2.98/3.19  thf('58', plain,
% 2.98/3.19      (((v1_partfun1 @ sk_C @ sk_A)
% 2.98/3.19        | (v1_xboole_0 @ sk_C)
% 2.98/3.19        | ~ (v1_funct_1 @ sk_C)
% 2.98/3.19        | ~ (v1_relat_1 @ sk_C))),
% 2.98/3.19      inference('sup-', [status(thm)], ['54', '57'])).
% 2.98/3.19  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['9', '10'])).
% 2.98/3.19  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['25', '26'])).
% 2.98/3.19  thf('61', plain, (((v1_partfun1 @ sk_C @ sk_A) | (v1_xboole_0 @ sk_C))),
% 2.98/3.19      inference('demod', [status(thm)], ['58', '59', '60'])).
% 2.98/3.19  thf('62', plain,
% 2.98/3.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.98/3.19      inference('demod', [status(thm)], ['21', '24', '27'])).
% 2.98/3.19  thf(cc1_funct_2, axiom,
% 2.98/3.19    (![A:$i,B:$i,C:$i]:
% 2.98/3.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.98/3.19       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 2.98/3.19         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 2.98/3.19  thf('63', plain,
% 2.98/3.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.98/3.19         (~ (v1_funct_1 @ X26)
% 2.98/3.19          | ~ (v1_partfun1 @ X26 @ X27)
% 2.98/3.19          | (v1_funct_2 @ X26 @ X27 @ X28)
% 2.98/3.19          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.98/3.19      inference('cnf', [status(esa)], [cc1_funct_2])).
% 2.98/3.19  thf('64', plain,
% 2.98/3.19      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 2.98/3.19        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 2.98/3.19        | ~ (v1_funct_1 @ sk_C))),
% 2.98/3.19      inference('sup-', [status(thm)], ['62', '63'])).
% 2.98/3.19  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['9', '10'])).
% 2.98/3.19  thf('66', plain,
% 2.98/3.19      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1) | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 2.98/3.19      inference('demod', [status(thm)], ['64', '65'])).
% 2.98/3.19  thf('67', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.98/3.19      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 2.98/3.19  thf('68', plain, (~ (v1_partfun1 @ sk_C @ sk_A)),
% 2.98/3.19      inference('clc', [status(thm)], ['66', '67'])).
% 2.98/3.19  thf('69', plain, ((v1_xboole_0 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['61', '68'])).
% 2.98/3.19  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 2.98/3.19      inference('demod', [status(thm)], ['38', '69'])).
% 2.98/3.19  thf('71', plain, (~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B_1)),
% 2.98/3.19      inference('demod', [status(thm)], ['33', '70'])).
% 2.98/3.19  thf('72', plain, ((v1_xboole_0 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['61', '68'])).
% 2.98/3.19  thf('73', plain,
% 2.98/3.19      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 2.98/3.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.98/3.19  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 2.98/3.19      inference('sup-', [status(thm)], ['72', '73'])).
% 2.98/3.19  thf('75', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1)),
% 2.98/3.19      inference('demod', [status(thm)], ['71', '74'])).
% 2.98/3.19  thf('76', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.98/3.19      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.98/3.19  thf(t5_funct_2, axiom,
% 2.98/3.19    (![A:$i,B:$i,C:$i]:
% 2.98/3.19     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 2.98/3.19       ( ( ( ![D:$i]:
% 2.98/3.19             ( ( r2_hidden @ D @ A ) =>
% 2.98/3.19               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 2.98/3.19           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 2.98/3.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.98/3.19           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 2.98/3.19  thf(zf_stmt_4, axiom,
% 2.98/3.19    (![D:$i,C:$i,B:$i,A:$i]:
% 2.98/3.19     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 2.98/3.19       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 2.98/3.19  thf('77', plain,
% 2.98/3.19      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 2.98/3.19         ((zip_tseitin_1 @ X46 @ X47 @ X48 @ X49) | (r2_hidden @ X46 @ X49))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.98/3.19  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 2.98/3.19  thf(zf_stmt_6, axiom,
% 2.98/3.19    (![C:$i,B:$i,A:$i]:
% 2.98/3.19     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 2.98/3.19       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.98/3.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.98/3.19  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 2.98/3.19  thf(zf_stmt_8, axiom,
% 2.98/3.19    (![A:$i,B:$i,C:$i]:
% 2.98/3.19     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.98/3.19       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 2.98/3.19           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 2.98/3.19         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 2.98/3.19  thf('78', plain,
% 2.98/3.19      (![X53 : $i, X54 : $i, X55 : $i]:
% 2.98/3.19         (((k1_relat_1 @ X54) != (X53))
% 2.98/3.19          | ~ (zip_tseitin_1 @ (sk_D_1 @ X54 @ X55 @ X53) @ X54 @ X55 @ X53)
% 2.98/3.19          | (zip_tseitin_2 @ X54 @ X55 @ X53)
% 2.98/3.19          | ~ (v1_funct_1 @ X54)
% 2.98/3.19          | ~ (v1_relat_1 @ X54))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_8])).
% 2.98/3.19  thf('79', plain,
% 2.98/3.19      (![X54 : $i, X55 : $i]:
% 2.98/3.19         (~ (v1_relat_1 @ X54)
% 2.98/3.19          | ~ (v1_funct_1 @ X54)
% 2.98/3.19          | (zip_tseitin_2 @ X54 @ X55 @ (k1_relat_1 @ X54))
% 2.98/3.19          | ~ (zip_tseitin_1 @ (sk_D_1 @ X54 @ X55 @ (k1_relat_1 @ X54)) @ 
% 2.98/3.19               X54 @ X55 @ (k1_relat_1 @ X54)))),
% 2.98/3.19      inference('simplify', [status(thm)], ['78'])).
% 2.98/3.19  thf('80', plain,
% 2.98/3.19      (![X0 : $i, X1 : $i]:
% 2.98/3.19         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.98/3.19           (k1_relat_1 @ X0))
% 2.98/3.19          | (zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 2.98/3.19          | ~ (v1_funct_1 @ X0)
% 2.98/3.19          | ~ (v1_relat_1 @ X0))),
% 2.98/3.19      inference('sup-', [status(thm)], ['77', '79'])).
% 2.98/3.19  thf('81', plain,
% 2.98/3.19      (![X0 : $i]:
% 2.98/3.19         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 2.98/3.19           (k1_relat_1 @ k1_xboole_0))
% 2.98/3.19          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.98/3.19          | ~ (v1_funct_1 @ k1_xboole_0)
% 2.98/3.19          | (zip_tseitin_2 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 2.98/3.19      inference('sup+', [status(thm)], ['76', '80'])).
% 2.98/3.19  thf('82', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.98/3.19      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.98/3.19  thf(t113_zfmisc_1, axiom,
% 2.98/3.19    (![A:$i,B:$i]:
% 2.98/3.19     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.98/3.19       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.98/3.19  thf('83', plain,
% 2.98/3.19      (![X8 : $i, X9 : $i]:
% 2.98/3.19         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 2.98/3.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.98/3.19  thf('84', plain,
% 2.98/3.19      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 2.98/3.19      inference('simplify', [status(thm)], ['83'])).
% 2.98/3.19  thf(fc6_relat_1, axiom,
% 2.98/3.19    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.98/3.19  thf('85', plain,
% 2.98/3.19      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 2.98/3.19      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.98/3.19  thf('86', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.98/3.19      inference('sup+', [status(thm)], ['84', '85'])).
% 2.98/3.19  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 2.98/3.19      inference('sup-', [status(thm)], ['9', '10'])).
% 2.98/3.19  thf('88', plain, (((sk_C) = (k1_xboole_0))),
% 2.98/3.19      inference('sup-', [status(thm)], ['72', '73'])).
% 2.98/3.19  thf('89', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.98/3.19      inference('demod', [status(thm)], ['87', '88'])).
% 2.98/3.19  thf('90', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.98/3.19      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.98/3.19  thf('91', plain,
% 2.98/3.19      (![X0 : $i]:
% 2.98/3.19         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 2.98/3.19          | (zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.98/3.19      inference('demod', [status(thm)], ['81', '82', '86', '89', '90'])).
% 2.98/3.19  thf(d1_xboole_0, axiom,
% 2.98/3.19    (![A:$i]:
% 2.98/3.19     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.98/3.19  thf('92', plain,
% 2.98/3.19      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.98/3.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.98/3.19  thf('93', plain,
% 2.98/3.19      (![X0 : $i]:
% 2.98/3.19         ((zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 2.98/3.19          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.98/3.19      inference('sup-', [status(thm)], ['91', '92'])).
% 2.98/3.19  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.98/3.19  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.98/3.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.98/3.19  thf('95', plain,
% 2.98/3.19      (![X0 : $i]: (zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.98/3.19      inference('demod', [status(thm)], ['93', '94'])).
% 2.98/3.19  thf('96', plain,
% 2.98/3.19      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.98/3.19         ((v1_funct_2 @ X50 @ X52 @ X51) | ~ (zip_tseitin_2 @ X50 @ X51 @ X52))),
% 2.98/3.19      inference('cnf', [status(esa)], [zf_stmt_6])).
% 2.98/3.19  thf('97', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.98/3.19      inference('sup-', [status(thm)], ['95', '96'])).
% 2.98/3.19  thf('98', plain, ($false), inference('demod', [status(thm)], ['75', '97'])).
% 2.98/3.19  
% 2.98/3.19  % SZS output end Refutation
% 2.98/3.19  
% 3.02/3.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
