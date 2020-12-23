%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F3VtrsAPkS

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  204 ( 224 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t51_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
          = ( k1_tarski @ B ) )
       => ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t51_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
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

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F3VtrsAPkS
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 57 iterations in 0.054s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.55  thf(t51_zfmisc_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.21/0.55       ( r2_hidden @ B @ A ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.21/0.55          ( r2_hidden @ B @ A ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t51_zfmisc_1])).
% 0.21/0.55  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t69_enumset1, axiom,
% 0.21/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.55  thf('1', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.55  thf(t70_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X19 : $i, X20 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.55  thf(d1_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.55       ( ![E:$i]:
% 0.21/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_2, axiom,
% 0.21/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_3, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.55       ( ![E:$i]:
% 0.21/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.55          | (r2_hidden @ X11 @ X15)
% 0.21/0.55          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.55         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.21/0.55          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.21/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['2', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 0.21/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.55  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t17_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.55  thf('12', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.55  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
