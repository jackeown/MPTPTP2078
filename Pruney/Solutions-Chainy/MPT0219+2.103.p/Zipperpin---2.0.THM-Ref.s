%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CJmCbAGWrS

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  72 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  479 ( 599 expanded)
%              Number of equality atoms :   49 (  65 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X6 )
      | ( X3 = X4 )
      | ( X3 = X5 )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X4 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X8 @ X9 @ X10 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CJmCbAGWrS
% 0.17/0.38  % Computer   : n016.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 12:08:34 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 59 iterations in 0.037s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(d1_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.53       ( ![E:$i]:
% 0.22/0.53         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.53           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, axiom,
% 0.22/0.53    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.53     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.53       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.53         ((zip_tseitin_0 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.53          | ((X3) = (X4))
% 0.22/0.53          | ((X3) = (X5))
% 0.22/0.53          | ((X3) = (X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t13_zfmisc_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.53         ( k1_tarski @ A ) ) =>
% 0.22/0.53       ( ( A ) = ( B ) ) ))).
% 0.22/0.53  thf(zf_stmt_1, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.53            ( k1_tarski @ A ) ) =>
% 0.22/0.53          ( ( A ) = ( B ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.53         = (k1_tarski @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.53  thf(t69_enumset1, axiom,
% 0.22/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.53  thf('2', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf(t71_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.22/0.53           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.22/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.53  thf(t70_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X21 : $i, X22 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf(t72_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.53         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 0.22/0.53           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.22/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.22/0.53  thf(t55_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.53     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.53       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.22/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18) @ 
% 0.22/0.53              (k1_tarski @ X19)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.22/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.22/0.53              (k1_tarski @ X4)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.22/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['5', '8'])).
% 0.22/0.53  thf(t73_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.53     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.22/0.53       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.22/0.53           = (k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 0.22/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.53         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 0.22/0.53           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.22/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.22/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.22/0.53      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.22/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['2', '13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_tarski @ X0 @ X1)
% 0.22/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.53  thf('17', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['1', '16'])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X21 : $i, X22 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.53  thf(zf_stmt_3, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.53       ( ![E:$i]:
% 0.22/0.53         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.53         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.22/0.53          | (r2_hidden @ X7 @ X11)
% 0.22/0.53          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.53         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.22/0.53          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.22/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.53          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['18', '20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.53         (((X3) != (X4)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X4 @ X4 @ X5 @ X2)),
% 0.22/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '23'])).
% 0.22/0.53  thf('25', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.53      inference('sup+', [status(thm)], ['17', '24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X21 : $i, X22 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X12 @ X11)
% 0.22/0.53          | ~ (zip_tseitin_0 @ X12 @ X8 @ X9 @ X10)
% 0.22/0.53          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.22/0.53         (~ (zip_tseitin_0 @ X12 @ X8 @ X9 @ X10)
% 0.22/0.53          | ~ (r2_hidden @ X12 @ (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.53          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['27', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.53          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['26', '30'])).
% 0.22/0.53  thf('32', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.22/0.53      inference('sup-', [status(thm)], ['25', '31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '32'])).
% 0.22/0.53  thf('34', plain, (((sk_B) = (sk_A))),
% 0.22/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.53  thf('35', plain, (((sk_A) != (sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.53  thf('36', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
