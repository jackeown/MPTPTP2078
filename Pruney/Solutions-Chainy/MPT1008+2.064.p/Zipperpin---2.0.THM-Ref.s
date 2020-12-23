%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5SfXjuOpfe

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:40 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 163 expanded)
%              Number of leaves         :   44 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  629 (1916 expanded)
%              Number of equality atoms :   55 ( 151 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v1_funct_2 @ X60 @ X58 @ X59 )
      | ( X58
        = ( k1_relset_1 @ X58 @ X59 @ X60 ) )
      | ~ ( zip_tseitin_2 @ X60 @ X59 @ X58 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('3',plain,(
    ! [X56: $i,X57: $i] :
      ( ( zip_tseitin_1 @ X56 @ X57 )
      | ( X56 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( zip_tseitin_1 @ X61 @ X62 )
      | ( zip_tseitin_2 @ X63 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k1_relset_1 @ X51 @ X52 @ X50 )
        = ( k1_relat_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('20',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X43 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X43 @ ( k1_tarski @ X42 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v4_relat_1 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('33',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k7_relat_1 @ X40 @ X41 ) )
      | ~ ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('37',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('39',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','28','29','30','39'])).

thf('41',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k2_relset_1 @ X54 @ X55 @ X53 )
        = ( k2_relat_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5SfXjuOpfe
% 0.15/0.36  % Computer   : n014.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:15:52 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 115 iterations in 0.141s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(t62_funct_2, conjecture,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.62         ( m1_subset_1 @
% 0.44/0.62           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.62         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.44/0.62           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.62            ( m1_subset_1 @
% 0.44/0.62              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.62          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.62            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.44/0.62              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.44/0.62  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(d1_funct_2, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_1, axiom,
% 0.44/0.62    (![C:$i,B:$i,A:$i]:
% 0.44/0.62     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.44/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.44/0.62         (~ (v1_funct_2 @ X60 @ X58 @ X59)
% 0.44/0.62          | ((X58) = (k1_relset_1 @ X58 @ X59 @ X60))
% 0.44/0.62          | ~ (zip_tseitin_2 @ X60 @ X59 @ X58))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.44/0.62        | ((k1_tarski @ sk_A)
% 0.44/0.62            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.62  thf(zf_stmt_2, axiom,
% 0.44/0.62    (![B:$i,A:$i]:
% 0.44/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.62       ( zip_tseitin_1 @ B @ A ) ))).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X56 : $i, X57 : $i]:
% 0.44/0.62         ((zip_tseitin_1 @ X56 @ X57) | ((X56) = (k1_xboole_0)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.44/0.62  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.44/0.62  thf(zf_stmt_5, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.44/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.44/0.62         (~ (zip_tseitin_1 @ X61 @ X62)
% 0.44/0.62          | (zip_tseitin_2 @ X63 @ X61 @ X62)
% 0.44/0.62          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61))))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.44/0.62        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      ((((sk_B) = (k1_xboole_0))
% 0.44/0.62        | (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['3', '6'])).
% 0.44/0.62  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('9', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.44/0.62         (((k1_relset_1 @ X51 @ X52 @ X50) = (k1_relat_1 @ X50))
% 0.44/0.62          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.62  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.44/0.62      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.44/0.62  thf(t69_enumset1, axiom,
% 0.44/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.44/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.62  thf(t70_enumset1, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i]:
% 0.44/0.62         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.44/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.62  thf(d1_enumset1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.62       ( ![E:$i]:
% 0.44/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.44/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.44/0.62  thf(zf_stmt_7, axiom,
% 0.44/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.44/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.44/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_8, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.62       ( ![E:$i]:
% 0.44/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.62         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.44/0.62          | (r2_hidden @ X5 @ X9)
% 0.44/0.62          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.62         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.44/0.62          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.44/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.62          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.44/0.62      inference('sup+', [status(thm)], ['15', '17'])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.62         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.44/0.62      inference('simplify', [status(thm)], ['19'])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['18', '20'])).
% 0.44/0.62  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['14', '21'])).
% 0.44/0.62  thf('23', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.44/0.62      inference('sup+', [status(thm)], ['13', '22'])).
% 0.44/0.62  thf(t168_funct_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.62       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.44/0.62         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.44/0.62           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (![X42 : $i, X43 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X42 @ (k1_relat_1 @ X43))
% 0.44/0.62          | ((k2_relat_1 @ (k7_relat_1 @ X43 @ (k1_tarski @ X42)))
% 0.44/0.62              = (k1_tarski @ (k1_funct_1 @ X43 @ X42)))
% 0.44/0.62          | ~ (v1_funct_1 @ X43)
% 0.44/0.62          | ~ (v1_relat_1 @ X43))),
% 0.44/0.62      inference('cnf', [status(esa)], [t168_funct_1])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.44/0.62        | ((k2_relat_1 @ (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.44/0.62            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(cc1_relset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( v1_relat_1 @ C ) ))).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.44/0.62         ((v1_relat_1 @ X44)
% 0.44/0.62          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.44/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.62  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.62  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.44/0.62      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(cc2_relset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.44/0.62         ((v4_relat_1 @ X47 @ X48)
% 0.44/0.62          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.44/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.62  thf('33', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.62  thf(t209_relat_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.62       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (![X40 : $i, X41 : $i]:
% 0.44/0.62         (((X40) = (k7_relat_1 @ X40 @ X41))
% 0.44/0.62          | ~ (v4_relat_1 @ X40 @ X41)
% 0.44/0.62          | ~ (v1_relat_1 @ X40))),
% 0.44/0.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.44/0.62        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.62  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.62  thf('37', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.62  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.44/0.62      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.44/0.62  thf('39', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.44/0.62      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['25', '28', '29', '30', '39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.44/0.62         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.44/0.62         (((k2_relset_1 @ X54 @ X55 @ X53) = (k2_relat_1 @ X53))
% 0.44/0.62          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['41', '44'])).
% 0.44/0.62  thf('46', plain, ($false),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['40', '45'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
