%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.93yWMnYpBl

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  66 expanded)
%              Number of leaves         :   30 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  461 ( 475 expanded)
%              Number of equality atoms :   45 (  47 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k4_xboole_0 @ X31 @ ( k1_tarski @ X32 ) )
        = X31 )
      | ( r2_hidden @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k6_subset_1 @ X31 @ ( k1_tarski @ X32 ) )
        = X31 )
      | ( r2_hidden @ X32 @ X31 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t52_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t52_ordinal1])).

thf('3',plain,(
    ( k6_subset_1 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X55: $i] :
      ( ( k1_ordinal1 @ X55 )
      = ( k2_xboole_0 @ X55 @ ( k1_tarski @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X2 @ X3 ) @ X3 )
      = ( k6_subset_1 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k6_subset_1 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ( k6_subset_1 @ sk_A @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['3','9'])).

thf('11',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(simplify,[status(thm)],['11'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X25 ) @ X27 )
      | ~ ( r2_hidden @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('20',plain,(
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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      | ( r2_hidden @ X41 @ X48 )
      | ( X48
       != ( k4_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X41 @ ( k4_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 ) )
      | ( zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X34 != X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X33: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ~ ( zip_tseitin_0 @ X33 @ X35 @ X36 @ X37 @ X38 @ X39 @ X33 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X56 @ X57 )
      | ~ ( r1_tarski @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( r1_tarski @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X3 ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X2 ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    $false ),
    inference('sup-',[status(thm)],['14','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.93yWMnYpBl
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 321 iterations in 0.113s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.56  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.20/0.56  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.56  thf(t65_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.56       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (![X31 : $i, X32 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ X31 @ (k1_tarski @ X32)) = (X31))
% 0.20/0.56          | (r2_hidden @ X32 @ X31))),
% 0.20/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.56  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X51 : $i, X52 : $i]:
% 0.20/0.56         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X31 : $i, X32 : $i]:
% 0.20/0.56         (((k6_subset_1 @ X31 @ (k1_tarski @ X32)) = (X31))
% 0.20/0.56          | (r2_hidden @ X32 @ X31))),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf(t52_ordinal1, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t52_ordinal1])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (((k6_subset_1 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d1_ordinal1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X55 : $i]:
% 0.20/0.56         ((k1_ordinal1 @ X55) = (k2_xboole_0 @ X55 @ (k1_tarski @ X55)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.56  thf(t40_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X3)
% 0.20/0.56           = (k4_xboole_0 @ X2 @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X51 : $i, X52 : $i]:
% 0.20/0.56         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X51 : $i, X52 : $i]:
% 0.20/0.56         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i]:
% 0.20/0.56         ((k6_subset_1 @ (k2_xboole_0 @ X2 @ X3) @ X3)
% 0.20/0.56           = (k6_subset_1 @ X2 @ X3))),
% 0.20/0.56      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k6_subset_1 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 0.20/0.56           = (k6_subset_1 @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '8'])).
% 0.20/0.56  thf('10', plain, (((k6_subset_1 @ sk_A @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['3', '9'])).
% 0.20/0.56  thf('11', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_A @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.56  thf('12', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.20/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.56  thf(l1_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X25 : $i, X27 : $i]:
% 0.20/0.56         ((r1_tarski @ (k1_tarski @ X25) @ X27) | ~ (r2_hidden @ X25 @ X27))),
% 0.20/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.56  thf('14', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf(t70_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.56  thf(t69_enumset1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.56  thf('16', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf(t71_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.56         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.56  thf(t72_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.56         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.56           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.56  thf(t73_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.56     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.56       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.56         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.56           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.56  thf(d4_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.56     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.20/0.56       ( ![H:$i]:
% 0.20/0.56         ( ( r2_hidden @ H @ G ) <=>
% 0.20/0.56           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.20/0.56                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_2, axiom,
% 0.20/0.56    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.56     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.20/0.56       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.20/0.56         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_3, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.56     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.20/0.56       ( ![H:$i]:
% 0.20/0.56         ( ( r2_hidden @ H @ G ) <=>
% 0.20/0.56           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 0.20/0.56         X48 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 0.20/0.56          | (r2_hidden @ X41 @ X48)
% 0.20/0.56          | ((X48) != (k4_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.56         ((r2_hidden @ X41 @ (k4_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42))
% 0.20/0.56          | (zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 0.20/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.56         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.56          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.20/0.56      inference('sup+', [status(thm)], ['20', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.56         (((X34) != (X33))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X33))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X33 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.56         ~ (zip_tseitin_0 @ X33 @ X35 @ X36 @ X37 @ X38 @ X39 @ X33)),
% 0.20/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.20/0.56      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.56  thf(t7_ordinal1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X56 : $i, X57 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X56 @ X57) | ~ (r1_tarski @ X57 @ X56))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         ~ (r1_tarski @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X4)),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         ~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X3)),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X2)),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '29'])).
% 0.20/0.56  thf('31', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '30'])).
% 0.20/0.56  thf('32', plain, ($false), inference('sup-', [status(thm)], ['14', '31'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
