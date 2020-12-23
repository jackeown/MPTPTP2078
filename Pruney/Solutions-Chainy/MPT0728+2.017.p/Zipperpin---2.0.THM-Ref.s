%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cZRQkSFCDe

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:40 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   50 (  50 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  409 ( 409 expanded)
%              Number of equality atoms :   35 (  35 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t10_ordinal1,conjecture,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t10_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X49: $i] :
      ( ( k1_ordinal1 @ X49 )
      = ( k2_xboole_0 @ X49 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(d5_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( ( I != G )
              & ( I != F )
              & ( I != E )
              & ( I != D )
              & ( I != C )
              & ( I != B )
              & ( I != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [I: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( I != A )
        & ( I != B )
        & ( I != C )
        & ( I != D )
        & ( I != E )
        & ( I != F )
        & ( I != G ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 )
      | ( r2_hidden @ X38 @ X46 )
      | ( X46
       != ( k5_enumset1 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( r2_hidden @ X38 @ ( k5_enumset1 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X30 != X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X29: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X29 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X29 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X0 @ ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cZRQkSFCDe
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.06/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.23  % Solved by: fo/fo7.sh
% 1.06/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.23  % done 621 iterations in 0.787s
% 1.06/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.23  % SZS output start Refutation
% 1.06/1.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.23  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.06/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.23  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.23  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.06/1.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.06/1.23  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.06/1.23  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.06/1.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 1.06/1.23                                               $i > $i > $o).
% 1.06/1.23  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.06/1.23  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.06/1.23  thf(t10_ordinal1, conjecture,
% 1.06/1.23    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 1.06/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.23    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 1.06/1.23    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 1.06/1.23  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf(d1_ordinal1, axiom,
% 1.06/1.23    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.06/1.23  thf('1', plain,
% 1.06/1.23      (![X49 : $i]:
% 1.06/1.23         ((k1_ordinal1 @ X49) = (k2_xboole_0 @ X49 @ (k1_tarski @ X49)))),
% 1.06/1.23      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.06/1.23  thf(t70_enumset1, axiom,
% 1.06/1.23    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.06/1.23  thf('2', plain,
% 1.06/1.23      (![X7 : $i, X8 : $i]:
% 1.06/1.23         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 1.06/1.23      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.06/1.23  thf(t69_enumset1, axiom,
% 1.06/1.23    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.06/1.23  thf('3', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.06/1.23      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.06/1.23  thf('4', plain,
% 1.06/1.23      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['2', '3'])).
% 1.06/1.23  thf(t71_enumset1, axiom,
% 1.06/1.23    (![A:$i,B:$i,C:$i]:
% 1.06/1.23     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.06/1.23  thf('5', plain,
% 1.06/1.23      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.06/1.23         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 1.06/1.23      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.06/1.23  thf(t72_enumset1, axiom,
% 1.06/1.23    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.23     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.06/1.23  thf('6', plain,
% 1.06/1.23      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.23         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 1.06/1.23           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 1.06/1.23      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.06/1.23  thf(t73_enumset1, axiom,
% 1.06/1.23    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.06/1.23     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.06/1.23       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.06/1.23  thf('7', plain,
% 1.06/1.23      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.23         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.06/1.23           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 1.06/1.23      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.06/1.23  thf(t74_enumset1, axiom,
% 1.06/1.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.06/1.23     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.06/1.23       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.06/1.23  thf('8', plain,
% 1.06/1.23      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.23         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 1.06/1.23           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 1.06/1.23      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.06/1.23  thf(d5_enumset1, axiom,
% 1.06/1.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.06/1.23     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 1.06/1.23       ( ![I:$i]:
% 1.06/1.23         ( ( r2_hidden @ I @ H ) <=>
% 1.06/1.23           ( ~( ( ( I ) != ( G ) ) & ( ( I ) != ( F ) ) & ( ( I ) != ( E ) ) & 
% 1.06/1.23                ( ( I ) != ( D ) ) & ( ( I ) != ( C ) ) & ( ( I ) != ( B ) ) & 
% 1.06/1.23                ( ( I ) != ( A ) ) ) ) ) ) ))).
% 1.06/1.23  thf(zf_stmt_1, type, zip_tseitin_0 :
% 1.06/1.23      $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 1.06/1.23  thf(zf_stmt_2, axiom,
% 1.06/1.23    (![I:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.06/1.23     ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) <=>
% 1.06/1.23       ( ( ( I ) != ( A ) ) & ( ( I ) != ( B ) ) & ( ( I ) != ( C ) ) & 
% 1.06/1.23         ( ( I ) != ( D ) ) & ( ( I ) != ( E ) ) & ( ( I ) != ( F ) ) & 
% 1.06/1.23         ( ( I ) != ( G ) ) ) ))).
% 1.06/1.23  thf(zf_stmt_3, axiom,
% 1.06/1.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.06/1.23     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 1.06/1.23       ( ![I:$i]:
% 1.06/1.23         ( ( r2_hidden @ I @ H ) <=>
% 1.06/1.23           ( ~( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.06/1.23  thf('9', plain,
% 1.06/1.23      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 1.06/1.23         X45 : $i, X46 : $i]:
% 1.06/1.23         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)
% 1.06/1.23          | (r2_hidden @ X38 @ X46)
% 1.06/1.23          | ((X46) != (k5_enumset1 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39)))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.06/1.23  thf('10', plain,
% 1.06/1.23      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 1.06/1.23         X45 : $i]:
% 1.06/1.23         ((r2_hidden @ X38 @ 
% 1.06/1.23           (k5_enumset1 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39))
% 1.06/1.23          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45))),
% 1.06/1.23      inference('simplify', [status(thm)], ['9'])).
% 1.06/1.23  thf('11', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.06/1.23         ((r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.06/1.23          | (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5))),
% 1.06/1.23      inference('sup+', [status(thm)], ['8', '10'])).
% 1.06/1.23  thf('12', plain,
% 1.06/1.23      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 1.06/1.23         X36 : $i]:
% 1.06/1.23         (((X30) != (X29))
% 1.06/1.23          | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X29))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.06/1.23  thf('13', plain,
% 1.06/1.23      (![X29 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.06/1.23         ~ (zip_tseitin_0 @ X29 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X29)),
% 1.06/1.23      inference('simplify', [status(thm)], ['12'])).
% 1.06/1.23  thf('14', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.23         (r2_hidden @ X0 @ (k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5))),
% 1.06/1.23      inference('sup-', [status(thm)], ['11', '13'])).
% 1.06/1.23  thf('15', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.23         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['7', '14'])).
% 1.06/1.23  thf('16', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.23         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['6', '15'])).
% 1.06/1.23  thf('17', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.23         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['5', '16'])).
% 1.06/1.23  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['4', '17'])).
% 1.06/1.23  thf(d3_xboole_0, axiom,
% 1.06/1.23    (![A:$i,B:$i,C:$i]:
% 1.06/1.23     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.06/1.23       ( ![D:$i]:
% 1.06/1.23         ( ( r2_hidden @ D @ C ) <=>
% 1.06/1.23           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.06/1.23  thf('19', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.23         (~ (r2_hidden @ X0 @ X1)
% 1.06/1.23          | (r2_hidden @ X0 @ X2)
% 1.06/1.23          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.06/1.23      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.06/1.23  thf('20', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.06/1.23         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.06/1.23      inference('simplify', [status(thm)], ['19'])).
% 1.06/1.23  thf('21', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.06/1.23      inference('sup-', [status(thm)], ['18', '20'])).
% 1.06/1.23  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['1', '21'])).
% 1.06/1.23  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 1.06/1.23  
% 1.06/1.23  % SZS output end Refutation
% 1.06/1.23  
% 1.06/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
