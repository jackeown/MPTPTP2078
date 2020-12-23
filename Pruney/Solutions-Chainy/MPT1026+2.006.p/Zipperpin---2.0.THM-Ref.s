%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RUznLaTGjZ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:52 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  154 (1227 expanded)
%              Number of leaves         :   37 ( 358 expanded)
%              Depth                    :   22
%              Number of atoms          : 1098 (13545 expanded)
%              Number of equality atoms :   34 ( 534 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

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
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X47 @ X46 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X47 @ X44 @ X45 ) @ X47 @ X44 @ X45 )
      | ( X46
       != ( k1_funct_2 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X44: $i,X45: $i,X47: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X47 @ X44 @ X45 ) @ X47 @ X44 @ X45 )
      | ~ ( r2_hidden @ X47 @ ( k1_funct_2 @ X45 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X39 = X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_1
    = ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_funct_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
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
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('17',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relat_1 @ X37 )
        = X40 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['13','31','32'])).

thf('34',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_partfun1 @ X28 @ X29 )
      | ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( v1_partfun1 @ X34 @ X35 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('49',plain,(
    ! [X50: $i] :
      ( ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('50',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('52',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('54',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','54'])).

thf('56',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['55','72'])).

thf('74',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['55','72'])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k1_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('80',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,
    ( ( k1_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('83',plain,
    ( ( k1_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('92',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X19 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['95'])).

thf('97',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('98',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['84','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('102',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X33 ) ) )
      | ( v1_partfun1 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('103',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['100','103'])).

thf('105',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','104'])).

thf('106',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','54'])).

thf('108',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('109',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['106','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('114',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['37','112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['34','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RUznLaTGjZ
% 0.15/0.34  % Computer   : n023.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:46:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.75/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.95  % Solved by: fo/fo7.sh
% 0.75/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.95  % done 475 iterations in 0.484s
% 0.75/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.95  % SZS output start Refutation
% 0.75/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.95  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.75/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.95  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.75/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.95  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.75/0.95  thf(t121_funct_2, conjecture,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.75/0.95       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.75/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.95    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.95        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.75/0.95          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.95            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.75/0.95    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.75/0.95  thf('0', plain,
% 0.75/0.95      ((~ (v1_funct_1 @ sk_C_1)
% 0.75/0.95        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.75/0.95        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('1', plain,
% 0.75/0.95      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.75/0.95         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('split', [status(esa)], ['0'])).
% 0.75/0.95  thf('2', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(d2_funct_2, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.75/0.95       ( ![D:$i]:
% 0.75/0.95         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.95           ( ?[E:$i]:
% 0.75/0.95             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.75/0.95               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.75/0.95               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.75/0.95  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.95  thf(zf_stmt_2, axiom,
% 0.75/0.95    (![E:$i,D:$i,B:$i,A:$i]:
% 0.75/0.95     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.75/0.95       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.75/0.95         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.75/0.95         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.75/0.95  thf(zf_stmt_3, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.75/0.95       ( ![D:$i]:
% 0.75/0.95         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.95           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.75/0.95  thf('3', plain,
% 0.75/0.95      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X47 @ X46)
% 0.75/0.95          | (zip_tseitin_0 @ (sk_E_1 @ X47 @ X44 @ X45) @ X47 @ X44 @ X45)
% 0.75/0.95          | ((X46) != (k1_funct_2 @ X45 @ X44)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.95  thf('4', plain,
% 0.75/0.95      (![X44 : $i, X45 : $i, X47 : $i]:
% 0.75/0.95         ((zip_tseitin_0 @ (sk_E_1 @ X47 @ X44 @ X45) @ X47 @ X44 @ X45)
% 0.75/0.95          | ~ (r2_hidden @ X47 @ (k1_funct_2 @ X45 @ X44)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['3'])).
% 0.75/0.95  thf('5', plain,
% 0.75/0.95      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1 @ sk_B @ sk_A)),
% 0.75/0.95      inference('sup-', [status(thm)], ['2', '4'])).
% 0.75/0.95  thf('6', plain,
% 0.75/0.95      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1 @ sk_B @ sk_A)),
% 0.75/0.95      inference('sup-', [status(thm)], ['2', '4'])).
% 0.75/0.95  thf('7', plain,
% 0.75/0.95      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.95         (((X39) = (X37)) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.95  thf('8', plain, (((sk_C_1) = (sk_E_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.95  thf('9', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.75/0.95      inference('demod', [status(thm)], ['5', '8'])).
% 0.75/0.95  thf('10', plain,
% 0.75/0.95      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.95         ((v1_funct_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.95  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.95  thf('12', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.75/0.95      inference('split', [status(esa)], ['0'])).
% 0.75/0.95  thf('13', plain, (((v1_funct_1 @ sk_C_1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.75/0.95  thf(d10_xboole_0, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.95  thf('14', plain,
% 0.75/0.95      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.95  thf('15', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.75/0.95      inference('simplify', [status(thm)], ['14'])).
% 0.75/0.95  thf('16', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.75/0.95      inference('demod', [status(thm)], ['5', '8'])).
% 0.75/0.95  thf('17', plain,
% 0.75/0.95      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.95         ((r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 0.75/0.95          | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.95  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.75/0.95      inference('sup-', [status(thm)], ['16', '17'])).
% 0.75/0.95  thf('19', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.75/0.95      inference('demod', [status(thm)], ['5', '8'])).
% 0.75/0.95  thf('20', plain,
% 0.75/0.95      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.95         (((k1_relat_1 @ X37) = (X40))
% 0.75/0.95          | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.95  thf('21', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.95  thf(t11_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ C ) =>
% 0.75/0.95       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.75/0.95           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.75/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.75/0.95  thf('22', plain,
% 0.75/0.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.75/0.95         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.75/0.95          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 0.75/0.95          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.75/0.95          | ~ (v1_relat_1 @ X25))),
% 0.75/0.95      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.75/0.95  thf('23', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (r1_tarski @ sk_A @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ sk_C_1)
% 0.75/0.95          | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.75/0.95          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ X1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.95  thf('24', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.75/0.95      inference('demod', [status(thm)], ['5', '8'])).
% 0.75/0.95  thf('25', plain,
% 0.75/0.95      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.95         ((v1_relat_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.95  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.95  thf('27', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (r1_tarski @ sk_A @ X0)
% 0.75/0.95          | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.75/0.95          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ X1))),
% 0.75/0.95      inference('demod', [status(thm)], ['23', '26'])).
% 0.75/0.95  thf('28', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.75/0.95          | ~ (r1_tarski @ sk_A @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['18', '27'])).
% 0.75/0.95  thf('29', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['15', '28'])).
% 0.75/0.95  thf('30', plain,
% 0.75/0.95      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.75/0.95         <= (~
% 0.75/0.95             ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.95               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.75/0.95      inference('split', [status(esa)], ['0'])).
% 0.75/0.95  thf('31', plain,
% 0.75/0.95      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.95  thf('32', plain,
% 0.75/0.95      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.75/0.95       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.75/0.95       ~ ((v1_funct_1 @ sk_C_1))),
% 0.75/0.95      inference('split', [status(esa)], ['0'])).
% 0.75/0.95  thf('33', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.75/0.95      inference('sat_resolution*', [status(thm)], ['13', '31', '32'])).
% 0.75/0.95  thf('34', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.75/0.95      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.75/0.95  thf('35', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['15', '28'])).
% 0.75/0.95  thf(cc1_funct_2, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.75/0.95         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.75/0.95  thf('36', plain,
% 0.75/0.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ X28)
% 0.75/0.95          | ~ (v1_partfun1 @ X28 @ X29)
% 0.75/0.95          | (v1_funct_2 @ X28 @ X29 @ X30)
% 0.75/0.95          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.75/0.95  thf('37', plain,
% 0.75/0.95      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.75/0.95        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.75/0.95        | ~ (v1_funct_1 @ sk_C_1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['35', '36'])).
% 0.75/0.95  thf('38', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.95  thf(t3_funct_2, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.95       ( ( v1_funct_1 @ A ) & 
% 0.75/0.95         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.75/0.95         ( m1_subset_1 @
% 0.75/0.95           A @ 
% 0.75/0.95           ( k1_zfmisc_1 @
% 0.75/0.95             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.75/0.95  thf('39', plain,
% 0.75/0.95      (![X50 : $i]:
% 0.75/0.95         ((m1_subset_1 @ X50 @ 
% 0.75/0.95           (k1_zfmisc_1 @ 
% 0.75/0.95            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 0.75/0.95          | ~ (v1_funct_1 @ X50)
% 0.75/0.95          | ~ (v1_relat_1 @ X50))),
% 0.75/0.95      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.75/0.95  thf('40', plain,
% 0.75/0.95      (((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.75/0.95        | ~ (v1_relat_1 @ sk_C_1)
% 0.75/0.95        | ~ (v1_funct_1 @ sk_C_1))),
% 0.75/0.95      inference('sup+', [status(thm)], ['38', '39'])).
% 0.75/0.95  thf('41', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.95  thf('42', plain,
% 0.75/0.95      (((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.75/0.95        | ~ (v1_relat_1 @ sk_C_1))),
% 0.75/0.95      inference('demod', [status(thm)], ['40', '41'])).
% 0.75/0.95  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.95  thf('44', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.95  thf(cc5_funct_2, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.95       ( ![C:$i]:
% 0.75/0.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.75/0.95             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.75/0.95  thf('45', plain,
% 0.75/0.95      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.75/0.95          | (v1_partfun1 @ X34 @ X35)
% 0.75/0.95          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.75/0.95          | ~ (v1_funct_1 @ X34)
% 0.75/0.95          | (v1_xboole_0 @ X36))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.75/0.95  thf('46', plain,
% 0.75/0.95      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.75/0.95        | ~ (v1_funct_1 @ sk_C_1)
% 0.75/0.95        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.75/0.95        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['44', '45'])).
% 0.75/0.95  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.95  thf('48', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.95  thf('49', plain,
% 0.75/0.95      (![X50 : $i]:
% 0.75/0.95         ((v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))
% 0.75/0.95          | ~ (v1_funct_1 @ X50)
% 0.75/0.95          | ~ (v1_relat_1 @ X50))),
% 0.75/0.95      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.75/0.95  thf('50', plain,
% 0.75/0.95      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.75/0.95        | ~ (v1_relat_1 @ sk_C_1)
% 0.75/0.95        | ~ (v1_funct_1 @ sk_C_1))),
% 0.75/0.95      inference('sup+', [status(thm)], ['48', '49'])).
% 0.75/0.95  thf('51', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.95  thf('52', plain,
% 0.75/0.95      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.75/0.95        | ~ (v1_relat_1 @ sk_C_1))),
% 0.75/0.95      inference('demod', [status(thm)], ['50', '51'])).
% 0.75/0.95  thf('53', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.95  thf('54', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 0.75/0.95      inference('demod', [status(thm)], ['52', '53'])).
% 0.75/0.95  thf('55', plain,
% 0.75/0.95      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['46', '47', '54'])).
% 0.75/0.95  thf('56', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.75/0.95      inference('simplify', [status(thm)], ['14'])).
% 0.75/0.95  thf(t3_subset, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.95  thf('57', plain,
% 0.75/0.95      (![X10 : $i, X12 : $i]:
% 0.75/0.95         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.75/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.95  thf('58', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.95  thf(cc4_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( v1_xboole_0 @ A ) =>
% 0.75/0.95       ( ![C:$i]:
% 0.75/0.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.75/0.95           ( v1_xboole_0 @ C ) ) ) ))).
% 0.75/0.95  thf('59', plain,
% 0.75/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X16)
% 0.75/0.95          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 0.75/0.95          | (v1_xboole_0 @ X17))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.75/0.95  thf('60', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['58', '59'])).
% 0.75/0.95  thf('61', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.95  thf('62', plain,
% 0.75/0.95      (![X10 : $i, X11 : $i]:
% 0.75/0.95         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.95  thf('63', plain,
% 0.75/0.95      ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['61', '62'])).
% 0.75/0.95  thf(d3_tarski, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( r1_tarski @ A @ B ) <=>
% 0.75/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/0.95  thf('64', plain,
% 0.75/0.95      (![X1 : $i, X3 : $i]:
% 0.75/0.95         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.75/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.95  thf('65', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.95  thf(t5_subset, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.75/0.95          ( v1_xboole_0 @ C ) ) ))).
% 0.75/0.95  thf('66', plain,
% 0.75/0.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X13 @ X14)
% 0.75/0.95          | ~ (v1_xboole_0 @ X15)
% 0.75/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t5_subset])).
% 0.75/0.95  thf('67', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.95  thf('68', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['64', '67'])).
% 0.75/0.95  thf('69', plain,
% 0.75/0.95      (![X4 : $i, X6 : $i]:
% 0.75/0.95         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.75/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.95  thf('70', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['68', '69'])).
% 0.75/0.95  thf('71', plain,
% 0.75/0.95      ((((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))
% 0.75/0.95        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['63', '70'])).
% 0.75/0.95  thf('72', plain,
% 0.75/0.95      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.75/0.95        | ((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['60', '71'])).
% 0.75/0.95  thf('73', plain,
% 0.75/0.95      (((v1_partfun1 @ sk_C_1 @ sk_A)
% 0.75/0.95        | ((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['55', '72'])).
% 0.75/0.95  thf('74', plain,
% 0.75/0.95      (((v1_partfun1 @ sk_C_1 @ sk_A)
% 0.75/0.95        | ((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['55', '72'])).
% 0.75/0.95  thf('75', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.95  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.95  thf('76', plain,
% 0.75/0.95      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.95         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.75/0.95          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.95  thf('77', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.75/0.95           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['75', '76'])).
% 0.75/0.95  thf('78', plain,
% 0.75/0.95      ((((k1_relset_1 @ sk_A @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 0.75/0.95          = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.75/0.95        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.75/0.95      inference('sup+', [status(thm)], ['74', '77'])).
% 0.75/0.95  thf('79', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.95  thf('80', plain,
% 0.75/0.95      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.95         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.75/0.95          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.95  thf('81', plain,
% 0.75/0.95      (((k1_relset_1 @ sk_A @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 0.75/0.95         = (k1_relat_1 @ sk_C_1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['79', '80'])).
% 0.75/0.95  thf('82', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.95  thf('83', plain,
% 0.75/0.95      (((k1_relset_1 @ sk_A @ (k2_relat_1 @ sk_C_1) @ sk_C_1) = (sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['81', '82'])).
% 0.75/0.95  thf('84', plain,
% 0.75/0.95      ((((sk_A) = (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.75/0.95        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['78', '83'])).
% 0.75/0.95  thf('85', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['58', '59'])).
% 0.75/0.95  thf('86', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['64', '67'])).
% 0.75/0.95  thf('87', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['68', '69'])).
% 0.75/0.95  thf('88', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['86', '87'])).
% 0.75/0.95  thf('89', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X0)
% 0.75/0.95          | ~ (v1_xboole_0 @ X2)
% 0.75/0.95          | ((k2_zfmisc_1 @ X1 @ X0) = (X2)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['85', '88'])).
% 0.75/0.95  thf('90', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.75/0.95           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['75', '76'])).
% 0.75/0.95  thf('91', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.95  thf(dt_k1_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.95  thf('92', plain,
% 0.75/0.95      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.95         ((m1_subset_1 @ (k1_relset_1 @ X19 @ X20 @ X21) @ (k1_zfmisc_1 @ X19))
% 0.75/0.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.75/0.95  thf('93', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 0.75/0.95          (k1_zfmisc_1 @ X1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['91', '92'])).
% 0.75/0.95  thf('94', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 0.75/0.95          (k1_zfmisc_1 @ X1))),
% 0.75/0.95      inference('sup+', [status(thm)], ['90', '93'])).
% 0.75/0.95  thf('95', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         ((m1_subset_1 @ (k1_relat_1 @ X0) @ (k1_zfmisc_1 @ X1))
% 0.75/0.95          | ~ (v1_xboole_0 @ X0)
% 0.75/0.95          | ~ (v1_xboole_0 @ X2))),
% 0.75/0.95      inference('sup+', [status(thm)], ['89', '94'])).
% 0.75/0.95  thf('96', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((m1_subset_1 @ (k1_relat_1 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.75/0.95          | ~ (v1_xboole_0 @ X1))),
% 0.75/0.95      inference('condensation', [status(thm)], ['95'])).
% 0.75/0.95  thf('97', plain,
% 0.75/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X16)
% 0.75/0.95          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 0.75/0.95          | (v1_xboole_0 @ X17))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.75/0.95  thf('98', plain,
% 0.75/0.95      (![X0 : $i, X2 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X2)
% 0.75/0.95          | (v1_xboole_0 @ (k1_relat_1 @ X2))
% 0.75/0.95          | ~ (v1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['96', '97'])).
% 0.75/0.95  thf('99', plain,
% 0.75/0.95      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.75/0.95      inference('condensation', [status(thm)], ['98'])).
% 0.75/0.95  thf('100', plain,
% 0.75/0.95      (((v1_xboole_0 @ sk_A)
% 0.75/0.95        | (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.75/0.95        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('sup+', [status(thm)], ['84', '99'])).
% 0.75/0.95  thf('101', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.95  thf(cc1_partfun1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( v1_xboole_0 @ A ) =>
% 0.75/0.95       ( ![C:$i]:
% 0.75/0.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.75/0.95  thf('102', plain,
% 0.75/0.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X31)
% 0.75/0.95          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X33)))
% 0.75/0.95          | (v1_partfun1 @ X32 @ X31))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.75/0.95  thf('103', plain, (((v1_partfun1 @ sk_C_1 @ sk_A) | ~ (v1_xboole_0 @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['101', '102'])).
% 0.75/0.95  thf('104', plain,
% 0.75/0.95      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))
% 0.75/0.95        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['100', '103'])).
% 0.75/0.95  thf('105', plain,
% 0.75/0.95      ((~ (v1_xboole_0 @ sk_C_1)
% 0.75/0.95        | (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.75/0.95        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['73', '104'])).
% 0.75/0.95  thf('106', plain,
% 0.75/0.95      (((v1_partfun1 @ sk_C_1 @ sk_A) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.75/0.95      inference('simplify', [status(thm)], ['105'])).
% 0.75/0.95  thf('107', plain,
% 0.75/0.95      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['46', '47', '54'])).
% 0.75/0.95  thf('108', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.95      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.95  thf('109', plain,
% 0.75/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.75/0.95         (~ (v1_xboole_0 @ X16)
% 0.75/0.95          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 0.75/0.95          | (v1_xboole_0 @ X17))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.75/0.95  thf('110', plain,
% 0.75/0.95      (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['108', '109'])).
% 0.75/0.95  thf('111', plain, (((v1_partfun1 @ sk_C_1 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['107', '110'])).
% 0.75/0.95  thf('112', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.75/0.95      inference('clc', [status(thm)], ['106', '111'])).
% 0.75/0.95  thf('113', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.95  thf('114', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.75/0.95      inference('demod', [status(thm)], ['37', '112', '113'])).
% 0.75/0.95  thf('115', plain, ($false), inference('demod', [status(thm)], ['34', '114'])).
% 0.75/0.95  
% 0.75/0.95  % SZS output end Refutation
% 0.75/0.95  
% 0.75/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
