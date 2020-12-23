%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2RJ7cOgrMz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:44 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   75 (  84 expanded)
%              Number of leaves         :   32 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  535 ( 676 expanded)
%              Number of equality atoms :   38 (  51 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(d4_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( ( H != F )
              & ( H != E )
              & ( H != D )
              & ( H != C )
              & ( H != B )
              & ( H != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      | ( r2_hidden @ X43 @ X50 )
      | ( X50
       != ( k4_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ X43 @ ( k4_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 ) )
      | ( zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X36 != X37 )
      | ~ ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X35: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ~ ( zip_tseitin_0 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X35 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf(t14_ordinal1,conjecture,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( A
       != ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t14_ordinal1])).

thf('13',plain,
    ( sk_A
    = ( k1_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('14',plain,(
    ! [X58: $i] :
      ( ( k1_ordinal1 @ X58 )
      = ( k2_xboole_0 @ X58 @ ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('16',plain,(
    ! [X34: $i] :
      ( r1_tarski @ X34 @ ( k1_zfmisc_1 @ ( k3_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ ( k1_tarski @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X53: $i,X54: $i] :
      ( ( m1_subset_1 @ X53 @ X54 )
      | ~ ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('33',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X36 != X35 )
      | ~ ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    ! [X35: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ~ ( zip_tseitin_0 @ X35 @ X37 @ X38 @ X39 @ X40 @ X41 @ X35 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( r2_hidden @ X59 @ X60 )
      | ~ ( r1_tarski @ X60 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( r1_tarski @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X3 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X2 ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2RJ7cOgrMz
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.81/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/0.99  % Solved by: fo/fo7.sh
% 0.81/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/0.99  % done 972 iterations in 0.516s
% 0.81/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/0.99  % SZS output start Refutation
% 0.81/0.99  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.81/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.81/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/0.99  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.81/0.99  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.81/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.81/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/0.99  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.81/0.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.81/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.81/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.81/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.81/0.99  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.81/0.99  thf(t70_enumset1, axiom,
% 0.81/0.99    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.81/0.99  thf('0', plain,
% 0.81/0.99      (![X5 : $i, X6 : $i]:
% 0.81/0.99         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.81/0.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.81/0.99  thf(t71_enumset1, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i]:
% 0.81/0.99     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.81/0.99  thf('1', plain,
% 0.81/0.99      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/0.99         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.81/0.99      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.81/0.99  thf(t72_enumset1, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/0.99     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.81/0.99  thf('2', plain,
% 0.81/0.99      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.81/0.99         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.81/0.99           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.81/0.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.81/0.99  thf(t73_enumset1, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.81/0.99     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.81/0.99       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.81/0.99  thf('3', plain,
% 0.81/0.99      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.81/0.99         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.81/0.99           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.81/0.99      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.81/0.99  thf(d4_enumset1, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.81/0.99     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.81/0.99       ( ![H:$i]:
% 0.81/0.99         ( ( r2_hidden @ H @ G ) <=>
% 0.81/0.99           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.81/0.99                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.81/0.99  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.81/0.99  thf(zf_stmt_1, axiom,
% 0.81/0.99    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.81/0.99     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.81/0.99       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.81/0.99         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.81/0.99  thf(zf_stmt_2, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.81/0.99     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.81/0.99       ( ![H:$i]:
% 0.81/0.99         ( ( r2_hidden @ H @ G ) <=>
% 0.81/0.99           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.81/0.99  thf('4', plain,
% 0.81/0.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, 
% 0.81/0.99         X50 : $i]:
% 0.81/0.99         ((zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.81/0.99          | (r2_hidden @ X43 @ X50)
% 0.81/0.99          | ((X50) != (k4_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.81/0.99  thf('5', plain,
% 0.81/0.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.81/0.99         ((r2_hidden @ X43 @ (k4_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44))
% 0.81/0.99          | (zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.81/0.99      inference('simplify', [status(thm)], ['4'])).
% 0.81/0.99  thf('6', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.81/0.99         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.81/0.99          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.81/0.99      inference('sup+', [status(thm)], ['3', '5'])).
% 0.81/0.99  thf('7', plain,
% 0.81/0.99      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.81/0.99         (((X36) != (X37))
% 0.81/0.99          | ~ (zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X35))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.81/0.99  thf('8', plain,
% 0.81/0.99      (![X35 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.81/0.99         ~ (zip_tseitin_0 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X35)),
% 0.81/0.99      inference('simplify', [status(thm)], ['7'])).
% 0.81/0.99  thf('9', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.81/0.99         (r2_hidden @ X4 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.81/0.99      inference('sup-', [status(thm)], ['6', '8'])).
% 0.81/0.99  thf('10', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/0.99         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.81/0.99      inference('sup+', [status(thm)], ['2', '9'])).
% 0.81/0.99  thf('11', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.99         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.81/0.99      inference('sup+', [status(thm)], ['1', '10'])).
% 0.81/0.99  thf('12', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.81/0.99      inference('sup+', [status(thm)], ['0', '11'])).
% 0.81/0.99  thf(t14_ordinal1, conjecture, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.81/0.99  thf(zf_stmt_3, negated_conjecture,
% 0.81/0.99    (~( ![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ) )),
% 0.81/0.99    inference('cnf.neg', [status(esa)], [t14_ordinal1])).
% 0.81/0.99  thf('13', plain, (((sk_A) = (k1_ordinal1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.81/0.99  thf(d1_ordinal1, axiom,
% 0.81/0.99    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.81/0.99  thf('14', plain,
% 0.81/0.99      (![X58 : $i]:
% 0.81/0.99         ((k1_ordinal1 @ X58) = (k2_xboole_0 @ X58 @ (k1_tarski @ X58)))),
% 0.81/0.99      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.81/0.99  thf(l51_zfmisc_1, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.81/0.99  thf('15', plain,
% 0.81/0.99      (![X32 : $i, X33 : $i]:
% 0.81/0.99         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 0.81/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.81/0.99  thf(t100_zfmisc_1, axiom,
% 0.81/0.99    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.81/0.99  thf('16', plain,
% 0.81/0.99      (![X34 : $i]: (r1_tarski @ X34 @ (k1_zfmisc_1 @ (k3_tarski @ X34)))),
% 0.81/0.99      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.81/0.99  thf('17', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]:
% 0.81/0.99         (r1_tarski @ (k2_tarski @ X1 @ X0) @ 
% 0.81/0.99          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.81/0.99      inference('sup+', [status(thm)], ['15', '16'])).
% 0.81/0.99  thf('18', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (r1_tarski @ (k2_tarski @ X0 @ (k1_tarski @ X0)) @ 
% 0.81/0.99          (k1_zfmisc_1 @ (k1_ordinal1 @ X0)))),
% 0.81/0.99      inference('sup+', [status(thm)], ['14', '17'])).
% 0.81/0.99  thf('19', plain,
% 0.81/0.99      ((r1_tarski @ (k2_tarski @ sk_A @ (k1_tarski @ sk_A)) @ 
% 0.81/0.99        (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('sup+', [status(thm)], ['13', '18'])).
% 0.81/0.99  thf(d3_tarski, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( r1_tarski @ A @ B ) <=>
% 0.81/0.99       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.81/0.99  thf('20', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.99         (~ (r2_hidden @ X0 @ X1)
% 0.81/0.99          | (r2_hidden @ X0 @ X2)
% 0.81/0.99          | ~ (r1_tarski @ X1 @ X2))),
% 0.81/0.99      inference('cnf', [status(esa)], [d3_tarski])).
% 0.81/0.99  thf('21', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.81/0.99          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ (k1_tarski @ sk_A))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.81/0.99  thf('22', plain, ((r2_hidden @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('sup-', [status(thm)], ['12', '21'])).
% 0.81/0.99  thf(t1_subset, axiom,
% 0.81/0.99    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.81/0.99  thf('23', plain,
% 0.81/0.99      (![X53 : $i, X54 : $i]:
% 0.81/0.99         ((m1_subset_1 @ X53 @ X54) | ~ (r2_hidden @ X53 @ X54))),
% 0.81/0.99      inference('cnf', [status(esa)], [t1_subset])).
% 0.81/0.99  thf('24', plain, ((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.81/0.99  thf(t3_subset, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.81/0.99  thf('25', plain,
% 0.81/0.99      (![X55 : $i, X56 : $i]:
% 0.81/0.99         ((r1_tarski @ X55 @ X56) | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56)))),
% 0.81/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/0.99  thf('26', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_A)),
% 0.81/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.81/0.99  thf('27', plain,
% 0.81/0.99      (![X5 : $i, X6 : $i]:
% 0.81/0.99         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.81/0.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.81/0.99  thf(t69_enumset1, axiom,
% 0.81/0.99    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.81/0.99  thf('28', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.81/0.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.81/0.99  thf('29', plain,
% 0.81/0.99      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.81/0.99      inference('sup+', [status(thm)], ['27', '28'])).
% 0.81/0.99  thf('30', plain,
% 0.81/0.99      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/0.99         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.81/0.99      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.81/0.99  thf('31', plain,
% 0.81/0.99      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.81/0.99         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.81/0.99           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.81/0.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.81/0.99  thf('32', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.81/0.99         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.81/0.99          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.81/0.99      inference('sup+', [status(thm)], ['3', '5'])).
% 0.81/0.99  thf('33', plain,
% 0.81/0.99      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.81/0.99         (((X36) != (X35))
% 0.81/0.99          | ~ (zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X35))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.81/0.99  thf('34', plain,
% 0.81/0.99      (![X35 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.81/0.99         ~ (zip_tseitin_0 @ X35 @ X37 @ X38 @ X39 @ X40 @ X41 @ X35)),
% 0.81/0.99      inference('simplify', [status(thm)], ['33'])).
% 0.81/0.99  thf('35', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.81/1.00         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.81/1.00      inference('sup-', [status(thm)], ['32', '34'])).
% 0.81/1.00  thf(t7_ordinal1, axiom,
% 0.81/1.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.00  thf('36', plain,
% 0.81/1.00      (![X59 : $i, X60 : $i]:
% 0.81/1.00         (~ (r2_hidden @ X59 @ X60) | ~ (r1_tarski @ X60 @ X59))),
% 0.81/1.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.81/1.00  thf('37', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.81/1.00         ~ (r1_tarski @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X4)),
% 0.81/1.00      inference('sup-', [status(thm)], ['35', '36'])).
% 0.81/1.00  thf('38', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.00         ~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X3)),
% 0.81/1.00      inference('sup-', [status(thm)], ['31', '37'])).
% 0.81/1.00  thf('39', plain,
% 0.81/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.00         ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X2)),
% 0.81/1.00      inference('sup-', [status(thm)], ['30', '38'])).
% 0.81/1.00  thf('40', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.81/1.00      inference('sup-', [status(thm)], ['29', '39'])).
% 0.81/1.00  thf('41', plain, ($false), inference('sup-', [status(thm)], ['26', '40'])).
% 0.81/1.00  
% 0.81/1.00  % SZS output end Refutation
% 0.81/1.00  
% 0.81/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
