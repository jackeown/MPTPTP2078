%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jzwaxTAQWw

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:53 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  189 (4793 expanded)
%              Number of leaves         :   42 (1345 expanded)
%              Depth                    :   28
%              Number of atoms          : 1223 (54823 expanded)
%              Number of equality atoms :   35 (2057 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C_2 @ ( k1_funct_2 @ sk_A @ sk_B ) ),
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
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X50 @ X49 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X50 @ X47 @ X48 ) @ X50 @ X47 @ X48 )
      | ( X49
       != ( k1_funct_2 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X47: $i,X48: $i,X50: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X50 @ X47 @ X48 ) @ X50 @ X47 @ X48 )
      | ~ ( r2_hidden @ X50 @ ( k1_funct_2 @ X48 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_2 @ sk_B @ sk_A ) @ sk_C_2 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_2 @ sk_B @ sk_A ) @ sk_C_2 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X42 = X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X42 @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_2
    = ( sk_E_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v1_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X42 @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
   <= ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('17',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ~ ( zip_tseitin_0 @ X40 @ X42 @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('20',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relat_1 @ X40 )
        = X43 )
      | ~ ( zip_tseitin_0 @ X40 @ X42 @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X33 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('25',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v1_relat_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X42 @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['13','31','32'])).

thf('34',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

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

thf('37',plain,(
    ! [X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( X20
       != ( k1_funct_1 @ X16 @ X21 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('38',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( v1_partfun1 @ X37 @ X38 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('53',plain,(
    ! [X55: $i] :
      ( ( v1_funct_2 @ X55 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('56',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('57',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('60',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_partfun1 @ X34 @ X35 )
      | ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('63',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('65',plain,(
    ~ ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('68',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('71',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('74',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('80',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['66','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['42','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('87',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('94',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['85','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['35','95'])).

thf('97',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( X0 = sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_A = sk_C_2 ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['69','70'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('104',plain,(
    ! [X54: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('105',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = sk_C_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X54: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('111',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('113',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X54: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('116',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( X0 = sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('120',plain,
    ( ( k2_relat_1 @ ( k6_partfun1 @ sk_C_2 ) )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('122',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ ( k6_partfun1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['69','70'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( k6_partfun1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ ( k6_partfun1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['109','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('130',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['69','70'])).

thf('131',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','82'])).

thf('133',plain,
    ( ( k6_partfun1 @ sk_C_2 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X53: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X53 ) @ X53 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('135',plain,(
    v1_partfun1 @ sk_C_2 @ sk_C_2 ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('137',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_partfun1 @ X34 @ X35 )
      | ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_2 )
      | ( v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['135','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('143',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['69','70'])).

thf('144',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0 ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['34','102','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jzwaxTAQWw
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.32/1.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.32/1.49  % Solved by: fo/fo7.sh
% 1.32/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.32/1.49  % done 1907 iterations in 1.034s
% 1.32/1.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.32/1.49  % SZS output start Refutation
% 1.32/1.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.32/1.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.32/1.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.32/1.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.32/1.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.32/1.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.32/1.49  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.32/1.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.32/1.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.32/1.49  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.32/1.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.32/1.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.32/1.49  thf(sk_B_type, type, sk_B: $i).
% 1.32/1.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.32/1.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.32/1.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.32/1.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.32/1.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.32/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.32/1.49  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 1.32/1.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.32/1.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.32/1.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.32/1.49  thf(t121_funct_2, conjecture,
% 1.32/1.49    (![A:$i,B:$i,C:$i]:
% 1.32/1.49     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.32/1.49       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.32/1.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.32/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.32/1.49    (~( ![A:$i,B:$i,C:$i]:
% 1.32/1.49        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.32/1.49          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.32/1.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 1.32/1.49    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 1.32/1.49  thf('0', plain,
% 1.32/1.49      ((~ (v1_funct_1 @ sk_C_2)
% 1.32/1.49        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 1.32/1.49        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 1.32/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.49  thf('1', plain,
% 1.32/1.49      ((~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))
% 1.32/1.49         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 1.32/1.49      inference('split', [status(esa)], ['0'])).
% 1.32/1.49  thf('2', plain, ((r2_hidden @ sk_C_2 @ (k1_funct_2 @ sk_A @ sk_B))),
% 1.32/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.49  thf(d2_funct_2, axiom,
% 1.32/1.49    (![A:$i,B:$i,C:$i]:
% 1.32/1.49     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.32/1.49       ( ![D:$i]:
% 1.32/1.49         ( ( r2_hidden @ D @ C ) <=>
% 1.32/1.49           ( ?[E:$i]:
% 1.32/1.49             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 1.32/1.49               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 1.32/1.49               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 1.32/1.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.32/1.49  thf(zf_stmt_2, axiom,
% 1.32/1.49    (![E:$i,D:$i,B:$i,A:$i]:
% 1.32/1.49     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 1.32/1.49       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 1.32/1.49         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 1.32/1.49         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 1.32/1.49  thf(zf_stmt_3, axiom,
% 1.32/1.49    (![A:$i,B:$i,C:$i]:
% 1.32/1.49     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.32/1.49       ( ![D:$i]:
% 1.32/1.49         ( ( r2_hidden @ D @ C ) <=>
% 1.32/1.49           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 1.32/1.49  thf('3', plain,
% 1.32/1.49      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.32/1.49         (~ (r2_hidden @ X50 @ X49)
% 1.32/1.49          | (zip_tseitin_0 @ (sk_E_1 @ X50 @ X47 @ X48) @ X50 @ X47 @ X48)
% 1.32/1.49          | ((X49) != (k1_funct_2 @ X48 @ X47)))),
% 1.32/1.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.32/1.49  thf('4', plain,
% 1.32/1.49      (![X47 : $i, X48 : $i, X50 : $i]:
% 1.32/1.49         ((zip_tseitin_0 @ (sk_E_1 @ X50 @ X47 @ X48) @ X50 @ X47 @ X48)
% 1.32/1.49          | ~ (r2_hidden @ X50 @ (k1_funct_2 @ X48 @ X47)))),
% 1.32/1.49      inference('simplify', [status(thm)], ['3'])).
% 1.32/1.49  thf('5', plain,
% 1.32/1.49      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_2 @ sk_B @ sk_A) @ sk_C_2 @ sk_B @ sk_A)),
% 1.32/1.49      inference('sup-', [status(thm)], ['2', '4'])).
% 1.32/1.49  thf('6', plain,
% 1.32/1.49      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_2 @ sk_B @ sk_A) @ sk_C_2 @ sk_B @ sk_A)),
% 1.32/1.49      inference('sup-', [status(thm)], ['2', '4'])).
% 1.32/1.49  thf('7', plain,
% 1.32/1.49      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.32/1.49         (((X42) = (X40)) | ~ (zip_tseitin_0 @ X40 @ X42 @ X41 @ X43))),
% 1.32/1.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.32/1.49  thf('8', plain, (((sk_C_2) = (sk_E_1 @ sk_C_2 @ sk_B @ sk_A))),
% 1.32/1.49      inference('sup-', [status(thm)], ['6', '7'])).
% 1.32/1.49  thf('9', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A)),
% 1.32/1.49      inference('demod', [status(thm)], ['5', '8'])).
% 1.32/1.49  thf('10', plain,
% 1.32/1.49      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.32/1.49         ((v1_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X42 @ X41 @ X43))),
% 1.32/1.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.32/1.49  thf('11', plain, ((v1_funct_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.49  thf('12', plain, ((~ (v1_funct_1 @ sk_C_2)) <= (~ ((v1_funct_1 @ sk_C_2)))),
% 1.32/1.49      inference('split', [status(esa)], ['0'])).
% 1.32/1.49  thf('13', plain, (((v1_funct_1 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['11', '12'])).
% 1.32/1.49  thf(d10_xboole_0, axiom,
% 1.32/1.49    (![A:$i,B:$i]:
% 1.32/1.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.32/1.49  thf('14', plain,
% 1.32/1.49      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.32/1.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.49  thf('15', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.32/1.49      inference('simplify', [status(thm)], ['14'])).
% 1.32/1.49  thf('16', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A)),
% 1.32/1.49      inference('demod', [status(thm)], ['5', '8'])).
% 1.32/1.49  thf('17', plain,
% 1.32/1.49      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.32/1.49         ((r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 1.32/1.49          | ~ (zip_tseitin_0 @ X40 @ X42 @ X41 @ X43))),
% 1.32/1.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.32/1.49  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 1.32/1.49      inference('sup-', [status(thm)], ['16', '17'])).
% 1.32/1.49  thf('19', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A)),
% 1.32/1.49      inference('demod', [status(thm)], ['5', '8'])).
% 1.32/1.49  thf('20', plain,
% 1.32/1.49      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.32/1.49         (((k1_relat_1 @ X40) = (X43))
% 1.32/1.49          | ~ (zip_tseitin_0 @ X40 @ X42 @ X41 @ X43))),
% 1.32/1.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.32/1.49  thf('21', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 1.32/1.49      inference('sup-', [status(thm)], ['19', '20'])).
% 1.32/1.49  thf(t11_relset_1, axiom,
% 1.32/1.49    (![A:$i,B:$i,C:$i]:
% 1.32/1.49     ( ( v1_relat_1 @ C ) =>
% 1.32/1.49       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.32/1.49           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.32/1.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.32/1.49  thf('22', plain,
% 1.32/1.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.32/1.49         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 1.32/1.49          | ~ (r1_tarski @ (k2_relat_1 @ X31) @ X33)
% 1.32/1.49          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.32/1.49          | ~ (v1_relat_1 @ X31))),
% 1.32/1.49      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.32/1.49  thf('23', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]:
% 1.32/1.49         (~ (r1_tarski @ sk_A @ X0)
% 1.32/1.49          | ~ (v1_relat_1 @ sk_C_2)
% 1.32/1.49          | (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 1.32/1.49          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X1))),
% 1.32/1.49      inference('sup-', [status(thm)], ['21', '22'])).
% 1.32/1.49  thf('24', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A)),
% 1.32/1.49      inference('demod', [status(thm)], ['5', '8'])).
% 1.32/1.49  thf('25', plain,
% 1.32/1.49      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.32/1.49         ((v1_relat_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X42 @ X41 @ X43))),
% 1.32/1.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.32/1.49  thf('26', plain, ((v1_relat_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['24', '25'])).
% 1.32/1.49  thf('27', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]:
% 1.32/1.49         (~ (r1_tarski @ sk_A @ X0)
% 1.32/1.49          | (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 1.32/1.49          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X1))),
% 1.32/1.49      inference('demod', [status(thm)], ['23', '26'])).
% 1.32/1.49  thf('28', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.32/1.49          | ~ (r1_tarski @ sk_A @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['18', '27'])).
% 1.32/1.49  thf('29', plain,
% 1.32/1.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['15', '28'])).
% 1.32/1.49  thf('30', plain,
% 1.32/1.49      ((~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 1.32/1.49         <= (~
% 1.32/1.49             ((m1_subset_1 @ sk_C_2 @ 
% 1.32/1.49               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 1.32/1.49      inference('split', [status(esa)], ['0'])).
% 1.32/1.49  thf('31', plain,
% 1.32/1.49      (((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 1.32/1.49      inference('sup-', [status(thm)], ['29', '30'])).
% 1.32/1.49  thf('32', plain,
% 1.32/1.49      (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)) | 
% 1.32/1.49       ~ ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 1.32/1.49       ~ ((v1_funct_1 @ sk_C_2))),
% 1.32/1.49      inference('split', [status(esa)], ['0'])).
% 1.32/1.49  thf('33', plain, (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 1.32/1.49      inference('sat_resolution*', [status(thm)], ['13', '31', '32'])).
% 1.32/1.49  thf('34', plain, (~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 1.32/1.49      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 1.32/1.49  thf(d3_tarski, axiom,
% 1.32/1.49    (![A:$i,B:$i]:
% 1.32/1.49     ( ( r1_tarski @ A @ B ) <=>
% 1.32/1.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.32/1.49  thf('35', plain,
% 1.32/1.49      (![X1 : $i, X3 : $i]:
% 1.32/1.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.32/1.49      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.49  thf('36', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 1.32/1.49      inference('sup-', [status(thm)], ['19', '20'])).
% 1.32/1.49  thf(d5_funct_1, axiom,
% 1.32/1.49    (![A:$i]:
% 1.32/1.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.49       ( ![B:$i]:
% 1.32/1.49         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.32/1.49           ( ![C:$i]:
% 1.32/1.49             ( ( r2_hidden @ C @ B ) <=>
% 1.32/1.49               ( ?[D:$i]:
% 1.32/1.49                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.32/1.49                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.32/1.49  thf('37', plain,
% 1.32/1.49      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 1.32/1.49         (((X18) != (k2_relat_1 @ X16))
% 1.32/1.49          | (r2_hidden @ X20 @ X18)
% 1.32/1.49          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 1.32/1.49          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 1.32/1.49          | ~ (v1_funct_1 @ X16)
% 1.32/1.49          | ~ (v1_relat_1 @ X16))),
% 1.32/1.49      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.32/1.49  thf('38', plain,
% 1.32/1.49      (![X16 : $i, X21 : $i]:
% 1.32/1.49         (~ (v1_relat_1 @ X16)
% 1.32/1.49          | ~ (v1_funct_1 @ X16)
% 1.32/1.49          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 1.32/1.49          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 1.32/1.49      inference('simplify', [status(thm)], ['37'])).
% 1.32/1.49  thf('39', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         (~ (r2_hidden @ X0 @ sk_A)
% 1.32/1.49          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 1.32/1.49          | ~ (v1_funct_1 @ sk_C_2)
% 1.32/1.49          | ~ (v1_relat_1 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['36', '38'])).
% 1.32/1.49  thf('40', plain, ((v1_funct_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.49  thf('41', plain, ((v1_relat_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['24', '25'])).
% 1.32/1.49  thf('42', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         (~ (r2_hidden @ X0 @ sk_A)
% 1.32/1.49          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 1.32/1.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.32/1.49  thf('43', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 1.32/1.49      inference('sup-', [status(thm)], ['19', '20'])).
% 1.32/1.49  thf(t3_funct_2, axiom,
% 1.32/1.49    (![A:$i]:
% 1.32/1.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.49       ( ( v1_funct_1 @ A ) & 
% 1.32/1.49         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.32/1.49         ( m1_subset_1 @
% 1.32/1.49           A @ 
% 1.32/1.49           ( k1_zfmisc_1 @
% 1.32/1.49             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.32/1.49  thf('44', plain,
% 1.32/1.49      (![X55 : $i]:
% 1.32/1.49         ((m1_subset_1 @ X55 @ 
% 1.32/1.49           (k1_zfmisc_1 @ 
% 1.32/1.49            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 1.32/1.49          | ~ (v1_funct_1 @ X55)
% 1.32/1.49          | ~ (v1_relat_1 @ X55))),
% 1.32/1.49      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.32/1.49  thf('45', plain,
% 1.32/1.49      (((m1_subset_1 @ sk_C_2 @ 
% 1.32/1.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2))))
% 1.32/1.49        | ~ (v1_relat_1 @ sk_C_2)
% 1.32/1.49        | ~ (v1_funct_1 @ sk_C_2))),
% 1.32/1.49      inference('sup+', [status(thm)], ['43', '44'])).
% 1.32/1.49  thf('46', plain, ((v1_relat_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['24', '25'])).
% 1.32/1.49  thf('47', plain, ((v1_funct_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.49  thf('48', plain,
% 1.32/1.49      ((m1_subset_1 @ sk_C_2 @ 
% 1.32/1.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2))))),
% 1.32/1.49      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.32/1.49  thf(cc5_funct_2, axiom,
% 1.32/1.49    (![A:$i,B:$i]:
% 1.32/1.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.32/1.49       ( ![C:$i]:
% 1.32/1.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.32/1.49           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.32/1.49             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.32/1.49  thf('49', plain,
% 1.32/1.49      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.32/1.49         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.32/1.49          | (v1_partfun1 @ X37 @ X38)
% 1.32/1.49          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.32/1.49          | ~ (v1_funct_1 @ X37)
% 1.32/1.49          | (v1_xboole_0 @ X39))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.32/1.49  thf('50', plain,
% 1.32/1.49      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 1.32/1.49        | ~ (v1_funct_1 @ sk_C_2)
% 1.32/1.49        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))
% 1.32/1.49        | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 1.32/1.49      inference('sup-', [status(thm)], ['48', '49'])).
% 1.32/1.49  thf('51', plain, ((v1_funct_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.49  thf('52', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 1.32/1.49      inference('sup-', [status(thm)], ['19', '20'])).
% 1.32/1.49  thf('53', plain,
% 1.32/1.49      (![X55 : $i]:
% 1.32/1.49         ((v1_funct_2 @ X55 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))
% 1.32/1.49          | ~ (v1_funct_1 @ X55)
% 1.32/1.49          | ~ (v1_relat_1 @ X55))),
% 1.32/1.49      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.32/1.49  thf('54', plain,
% 1.32/1.49      (((v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))
% 1.32/1.49        | ~ (v1_relat_1 @ sk_C_2)
% 1.32/1.49        | ~ (v1_funct_1 @ sk_C_2))),
% 1.32/1.49      inference('sup+', [status(thm)], ['52', '53'])).
% 1.32/1.49  thf('55', plain, ((v1_relat_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['24', '25'])).
% 1.32/1.49  thf('56', plain, ((v1_funct_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.49  thf('57', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))),
% 1.32/1.49      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.32/1.49  thf('58', plain,
% 1.32/1.49      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 1.32/1.49      inference('demod', [status(thm)], ['50', '51', '57'])).
% 1.32/1.49  thf('59', plain,
% 1.32/1.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['15', '28'])).
% 1.32/1.49  thf(cc1_funct_2, axiom,
% 1.32/1.49    (![A:$i,B:$i,C:$i]:
% 1.32/1.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.32/1.49       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.32/1.49         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.32/1.49  thf('60', plain,
% 1.32/1.49      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.32/1.49         (~ (v1_funct_1 @ X34)
% 1.32/1.49          | ~ (v1_partfun1 @ X34 @ X35)
% 1.32/1.49          | (v1_funct_2 @ X34 @ X35 @ X36)
% 1.32/1.49          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.32/1.49  thf('61', plain,
% 1.32/1.49      (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 1.32/1.49        | ~ (v1_partfun1 @ sk_C_2 @ sk_A)
% 1.32/1.49        | ~ (v1_funct_1 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['59', '60'])).
% 1.32/1.49  thf('62', plain, ((v1_funct_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.49  thf('63', plain,
% 1.32/1.49      (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B) | ~ (v1_partfun1 @ sk_C_2 @ sk_A))),
% 1.32/1.49      inference('demod', [status(thm)], ['61', '62'])).
% 1.32/1.49  thf('64', plain, (~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 1.32/1.49      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 1.32/1.49  thf('65', plain, (~ (v1_partfun1 @ sk_C_2 @ sk_A)),
% 1.32/1.49      inference('clc', [status(thm)], ['63', '64'])).
% 1.32/1.49  thf('66', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['58', '65'])).
% 1.32/1.49  thf('67', plain,
% 1.32/1.49      ((m1_subset_1 @ sk_C_2 @ 
% 1.32/1.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2))))),
% 1.32/1.49      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.32/1.49  thf(cc4_relset_1, axiom,
% 1.32/1.49    (![A:$i,B:$i]:
% 1.32/1.49     ( ( v1_xboole_0 @ A ) =>
% 1.32/1.49       ( ![C:$i]:
% 1.32/1.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.32/1.49           ( v1_xboole_0 @ C ) ) ) ))).
% 1.32/1.49  thf('68', plain,
% 1.32/1.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X28)
% 1.32/1.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 1.32/1.49          | (v1_xboole_0 @ X29))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.32/1.49  thf('69', plain,
% 1.32/1.49      (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_2)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['67', '68'])).
% 1.32/1.49  thf('70', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['58', '65'])).
% 1.32/1.49  thf('71', plain, ((v1_xboole_0 @ sk_C_2)),
% 1.32/1.49      inference('demod', [status(thm)], ['69', '70'])).
% 1.32/1.49  thf('72', plain,
% 1.32/1.49      (![X1 : $i, X3 : $i]:
% 1.32/1.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.32/1.49      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.49  thf('73', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.32/1.49      inference('simplify', [status(thm)], ['14'])).
% 1.32/1.49  thf(t3_subset, axiom,
% 1.32/1.49    (![A:$i,B:$i]:
% 1.32/1.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.32/1.49  thf('74', plain,
% 1.32/1.49      (![X7 : $i, X9 : $i]:
% 1.32/1.49         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.32/1.49      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.49  thf('75', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['73', '74'])).
% 1.32/1.49  thf(t5_subset, axiom,
% 1.32/1.49    (![A:$i,B:$i,C:$i]:
% 1.32/1.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.32/1.49          ( v1_xboole_0 @ C ) ) ))).
% 1.32/1.49  thf('76', plain,
% 1.32/1.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.32/1.49         (~ (r2_hidden @ X10 @ X11)
% 1.32/1.49          | ~ (v1_xboole_0 @ X12)
% 1.32/1.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.32/1.49      inference('cnf', [status(esa)], [t5_subset])).
% 1.32/1.49  thf('77', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['75', '76'])).
% 1.32/1.49  thf('78', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['72', '77'])).
% 1.32/1.49  thf('79', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['72', '77'])).
% 1.32/1.49  thf('80', plain,
% 1.32/1.49      (![X4 : $i, X6 : $i]:
% 1.32/1.49         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.32/1.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.49  thf('81', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['79', '80'])).
% 1.32/1.49  thf('82', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['78', '81'])).
% 1.32/1.49  thf('83', plain, (![X0 : $i]: (((X0) = (sk_C_2)) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['71', '82'])).
% 1.32/1.49  thf('84', plain, (((k2_relat_1 @ sk_C_2) = (sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['66', '83'])).
% 1.32/1.49  thf('85', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         (~ (r2_hidden @ X0 @ sk_A)
% 1.32/1.49          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_C_2))),
% 1.32/1.49      inference('demod', [status(thm)], ['42', '84'])).
% 1.32/1.49  thf('86', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['73', '74'])).
% 1.32/1.49  thf('87', plain,
% 1.32/1.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X28)
% 1.32/1.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 1.32/1.49          | (v1_xboole_0 @ X29))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.32/1.49  thf('88', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]:
% 1.32/1.49         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['86', '87'])).
% 1.32/1.49  thf('89', plain,
% 1.32/1.49      ((m1_subset_1 @ sk_C_2 @ 
% 1.32/1.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2))))),
% 1.32/1.49      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.32/1.49  thf('90', plain,
% 1.32/1.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.32/1.49         (~ (r2_hidden @ X10 @ X11)
% 1.32/1.49          | ~ (v1_xboole_0 @ X12)
% 1.32/1.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.32/1.49      inference('cnf', [status(esa)], [t5_subset])).
% 1.32/1.49  thf('91', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2)))
% 1.32/1.49          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['89', '90'])).
% 1.32/1.49  thf('92', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['88', '91'])).
% 1.32/1.49  thf('93', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['58', '65'])).
% 1.32/1.49  thf('94', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_2)),
% 1.32/1.49      inference('demod', [status(thm)], ['92', '93'])).
% 1.32/1.49  thf('95', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 1.32/1.49      inference('clc', [status(thm)], ['85', '94'])).
% 1.32/1.49  thf('96', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 1.32/1.49      inference('sup-', [status(thm)], ['35', '95'])).
% 1.32/1.49  thf('97', plain,
% 1.32/1.49      (![X1 : $i, X3 : $i]:
% 1.32/1.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.32/1.49      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.49  thf('98', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_2)),
% 1.32/1.49      inference('demod', [status(thm)], ['92', '93'])).
% 1.32/1.49  thf('99', plain, (![X0 : $i]: (r1_tarski @ sk_C_2 @ X0)),
% 1.32/1.49      inference('sup-', [status(thm)], ['97', '98'])).
% 1.32/1.49  thf('100', plain,
% 1.32/1.49      (![X4 : $i, X6 : $i]:
% 1.32/1.49         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.32/1.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.49  thf('101', plain,
% 1.32/1.49      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_2) | ((X0) = (sk_C_2)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['99', '100'])).
% 1.32/1.49  thf('102', plain, (((sk_A) = (sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['96', '101'])).
% 1.32/1.49  thf('103', plain, ((v1_xboole_0 @ sk_C_2)),
% 1.32/1.49      inference('demod', [status(thm)], ['69', '70'])).
% 1.32/1.49  thf(dt_k6_partfun1, axiom,
% 1.32/1.49    (![A:$i]:
% 1.32/1.49     ( ( m1_subset_1 @
% 1.32/1.49         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.32/1.49       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.32/1.49  thf('104', plain,
% 1.32/1.49      (![X54 : $i]:
% 1.32/1.49         (m1_subset_1 @ (k6_partfun1 @ X54) @ 
% 1.32/1.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X54)))),
% 1.32/1.49      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.32/1.49  thf('105', plain,
% 1.32/1.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X28)
% 1.32/1.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 1.32/1.49          | (v1_xboole_0 @ X29))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.32/1.49  thf('106', plain,
% 1.32/1.49      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['104', '105'])).
% 1.32/1.49  thf('107', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['78', '81'])).
% 1.32/1.49  thf('108', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X0)
% 1.32/1.49          | ~ (v1_xboole_0 @ X1)
% 1.32/1.49          | ((k6_partfun1 @ X0) = (X1)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['106', '107'])).
% 1.32/1.49  thf('109', plain,
% 1.32/1.49      (![X0 : $i]: (((k6_partfun1 @ X0) = (sk_C_2)) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['103', '108'])).
% 1.32/1.49  thf('110', plain,
% 1.32/1.49      (![X54 : $i]:
% 1.32/1.49         (m1_subset_1 @ (k6_partfun1 @ X54) @ 
% 1.32/1.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X54)))),
% 1.32/1.49      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.32/1.49  thf(cc2_relset_1, axiom,
% 1.32/1.49    (![A:$i,B:$i,C:$i]:
% 1.32/1.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.32/1.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.32/1.49  thf('111', plain,
% 1.32/1.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.32/1.49         ((v5_relat_1 @ X25 @ X27)
% 1.32/1.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.32/1.49  thf('112', plain, (![X0 : $i]: (v5_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.32/1.49      inference('sup-', [status(thm)], ['110', '111'])).
% 1.32/1.49  thf(d19_relat_1, axiom,
% 1.32/1.49    (![A:$i,B:$i]:
% 1.32/1.49     ( ( v1_relat_1 @ B ) =>
% 1.32/1.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.32/1.49  thf('113', plain,
% 1.32/1.49      (![X13 : $i, X14 : $i]:
% 1.32/1.49         (~ (v5_relat_1 @ X13 @ X14)
% 1.32/1.49          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.32/1.49          | ~ (v1_relat_1 @ X13))),
% 1.32/1.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.32/1.49  thf('114', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.32/1.49          | (r1_tarski @ (k2_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['112', '113'])).
% 1.32/1.49  thf('115', plain,
% 1.32/1.49      (![X54 : $i]:
% 1.32/1.49         (m1_subset_1 @ (k6_partfun1 @ X54) @ 
% 1.32/1.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X54)))),
% 1.32/1.49      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.32/1.49  thf(cc1_relset_1, axiom,
% 1.32/1.49    (![A:$i,B:$i,C:$i]:
% 1.32/1.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.32/1.49       ( v1_relat_1 @ C ) ))).
% 1.32/1.49  thf('116', plain,
% 1.32/1.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.32/1.49         ((v1_relat_1 @ X22)
% 1.32/1.49          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.32/1.49  thf('117', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['115', '116'])).
% 1.32/1.49  thf('118', plain,
% 1.32/1.49      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k6_partfun1 @ X0)) @ X0)),
% 1.32/1.49      inference('demod', [status(thm)], ['114', '117'])).
% 1.32/1.49  thf('119', plain,
% 1.32/1.49      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_2) | ((X0) = (sk_C_2)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['99', '100'])).
% 1.32/1.49  thf('120', plain, (((k2_relat_1 @ (k6_partfun1 @ sk_C_2)) = (sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['118', '119'])).
% 1.32/1.49  thf('121', plain,
% 1.32/1.49      (![X55 : $i]:
% 1.32/1.49         ((m1_subset_1 @ X55 @ 
% 1.32/1.49           (k1_zfmisc_1 @ 
% 1.32/1.49            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 1.32/1.49          | ~ (v1_funct_1 @ X55)
% 1.32/1.49          | ~ (v1_relat_1 @ X55))),
% 1.32/1.49      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.32/1.49  thf('122', plain,
% 1.32/1.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X28)
% 1.32/1.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 1.32/1.49          | (v1_xboole_0 @ X29))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.32/1.49  thf('123', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         (~ (v1_relat_1 @ X0)
% 1.32/1.49          | ~ (v1_funct_1 @ X0)
% 1.32/1.49          | (v1_xboole_0 @ X0)
% 1.32/1.49          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['121', '122'])).
% 1.32/1.49  thf('124', plain,
% 1.32/1.49      ((~ (v1_xboole_0 @ sk_C_2)
% 1.32/1.49        | (v1_xboole_0 @ (k6_partfun1 @ sk_C_2))
% 1.32/1.49        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_C_2))
% 1.32/1.49        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_C_2)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['120', '123'])).
% 1.32/1.49  thf('125', plain, ((v1_xboole_0 @ sk_C_2)),
% 1.32/1.49      inference('demod', [status(thm)], ['69', '70'])).
% 1.32/1.49  thf('126', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['115', '116'])).
% 1.32/1.49  thf('127', plain,
% 1.32/1.49      (((v1_xboole_0 @ (k6_partfun1 @ sk_C_2))
% 1.32/1.49        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_C_2)))),
% 1.32/1.49      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.32/1.49  thf('128', plain,
% 1.32/1.49      ((~ (v1_funct_1 @ sk_C_2)
% 1.32/1.49        | ~ (v1_xboole_0 @ sk_C_2)
% 1.32/1.49        | (v1_xboole_0 @ (k6_partfun1 @ sk_C_2)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['109', '127'])).
% 1.32/1.49  thf('129', plain, ((v1_funct_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.49  thf('130', plain, ((v1_xboole_0 @ sk_C_2)),
% 1.32/1.49      inference('demod', [status(thm)], ['69', '70'])).
% 1.32/1.49  thf('131', plain, ((v1_xboole_0 @ (k6_partfun1 @ sk_C_2))),
% 1.32/1.49      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.32/1.49  thf('132', plain, (![X0 : $i]: (((X0) = (sk_C_2)) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['71', '82'])).
% 1.32/1.49  thf('133', plain, (((k6_partfun1 @ sk_C_2) = (sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['131', '132'])).
% 1.32/1.49  thf('134', plain, (![X53 : $i]: (v1_partfun1 @ (k6_partfun1 @ X53) @ X53)),
% 1.32/1.49      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.32/1.49  thf('135', plain, ((v1_partfun1 @ sk_C_2 @ sk_C_2)),
% 1.32/1.49      inference('sup+', [status(thm)], ['133', '134'])).
% 1.32/1.49  thf('136', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.49      inference('sup-', [status(thm)], ['72', '77'])).
% 1.32/1.49  thf('137', plain,
% 1.32/1.49      (![X7 : $i, X9 : $i]:
% 1.32/1.49         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.32/1.49      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.49  thf('138', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.32/1.49      inference('sup-', [status(thm)], ['136', '137'])).
% 1.32/1.49  thf('139', plain,
% 1.32/1.49      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.32/1.49         (~ (v1_funct_1 @ X34)
% 1.32/1.49          | ~ (v1_partfun1 @ X34 @ X35)
% 1.32/1.49          | (v1_funct_2 @ X34 @ X35 @ X36)
% 1.32/1.49          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.32/1.49      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.32/1.49  thf('140', plain,
% 1.32/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.49         (~ (v1_xboole_0 @ X2)
% 1.32/1.49          | (v1_funct_2 @ X2 @ X1 @ X0)
% 1.32/1.49          | ~ (v1_partfun1 @ X2 @ X1)
% 1.32/1.49          | ~ (v1_funct_1 @ X2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['138', '139'])).
% 1.32/1.49  thf('141', plain,
% 1.32/1.49      (![X0 : $i]:
% 1.32/1.49         (~ (v1_funct_1 @ sk_C_2)
% 1.32/1.49          | (v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0)
% 1.32/1.49          | ~ (v1_xboole_0 @ sk_C_2))),
% 1.32/1.49      inference('sup-', [status(thm)], ['135', '140'])).
% 1.32/1.49  thf('142', plain, ((v1_funct_1 @ sk_C_2)),
% 1.32/1.49      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.49  thf('143', plain, ((v1_xboole_0 @ sk_C_2)),
% 1.32/1.49      inference('demod', [status(thm)], ['69', '70'])).
% 1.32/1.49  thf('144', plain, (![X0 : $i]: (v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0)),
% 1.32/1.49      inference('demod', [status(thm)], ['141', '142', '143'])).
% 1.32/1.49  thf('145', plain, ($false),
% 1.32/1.49      inference('demod', [status(thm)], ['34', '102', '144'])).
% 1.32/1.49  
% 1.32/1.49  % SZS output end Refutation
% 1.32/1.49  
% 1.32/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
