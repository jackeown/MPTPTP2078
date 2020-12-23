%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qK9zEyPqTL

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  387 ( 475 expanded)
%              Number of equality atoms :   42 (  52 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X28 ) @ ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t137_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X26 @ X25 ) @ ( k2_tarski @ X27 @ X25 ) )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k2_tarski @ X21 @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X26 @ X25 @ X27 @ X25 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X26 @ X25 @ X27 @ X25 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','23'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qK9zEyPqTL
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:58:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 252 iterations in 0.129s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.59  thf(t13_zfmisc_1, conjecture,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.59         ( k1_tarski @ A ) ) =>
% 0.20/0.59       ( ( A ) = ( B ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i,B:$i]:
% 0.20/0.59        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.59            ( k1_tarski @ A ) ) =>
% 0.20/0.59          ( ( A ) = ( B ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.59         = (k1_tarski @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t69_enumset1, axiom,
% 0.20/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.59  thf('1', plain, (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.20/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.59  thf(t70_enumset1, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      (![X38 : $i, X39 : $i]:
% 0.20/0.59         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.20/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.59  thf(t44_enumset1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.59     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.59       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.59         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 0.20/0.59           = (k2_xboole_0 @ (k1_tarski @ X28) @ (k1_enumset1 @ X29 @ X30 @ X31)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.20/0.59           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.59  thf(t71_enumset1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.59         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 0.20/0.59           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 0.20/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.59  thf(t137_enumset1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.20/0.59       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.59         ((k2_xboole_0 @ (k2_tarski @ X26 @ X25) @ (k2_tarski @ X27 @ X25))
% 0.20/0.59           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.20/0.59      inference('cnf', [status(esa)], [t137_enumset1])).
% 0.20/0.59  thf(l53_enumset1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.59     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.59       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.20/0.59  thf('7', plain,
% 0.20/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.59         ((k2_enumset1 @ X21 @ X22 @ X23 @ X24)
% 0.20/0.59           = (k2_xboole_0 @ (k2_tarski @ X21 @ X22) @ (k2_tarski @ X23 @ X24)))),
% 0.20/0.59      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.59         ((k2_enumset1 @ X26 @ X25 @ X27 @ X25)
% 0.20/0.59           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.20/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['5', '8'])).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      (![X38 : $i, X39 : $i]:
% 0.20/0.59         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.20/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.20/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.59         ((k2_enumset1 @ X26 @ X25 @ X27 @ X25)
% 0.20/0.59           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.20/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k2_enumset1 @ X0 @ X1 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (![X38 : $i, X39 : $i]:
% 0.20/0.59         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.20/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.59  thf(d1_enumset1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.59       ( ![E:$i]:
% 0.20/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.59  thf(zf_stmt_2, axiom,
% 0.20/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_3, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.59       ( ![E:$i]:
% 0.20/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.59         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.59          | (r2_hidden @ X9 @ X13)
% 0.20/0.59          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.59         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.20/0.59          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.20/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['14', '16'])).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.59         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.20/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (r2_hidden @ X0 @ (k2_enumset1 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['13', '20'])).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (r2_hidden @ X0 @ 
% 0.20/0.59          (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['4', '21'])).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['1', '22'])).
% 0.20/0.59  thf('24', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.59      inference('sup+', [status(thm)], ['0', '23'])).
% 0.20/0.59  thf(d1_tarski, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.59  thf('25', plain,
% 0.20/0.59      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X19 @ X18)
% 0.20/0.59          | ((X19) = (X16))
% 0.20/0.59          | ((X18) != (k1_tarski @ X16)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      (![X16 : $i, X19 : $i]:
% 0.20/0.59         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.59  thf('27', plain, (((sk_B) = (sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.59  thf('28', plain, (((sk_A) != (sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('29', plain, ($false),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
