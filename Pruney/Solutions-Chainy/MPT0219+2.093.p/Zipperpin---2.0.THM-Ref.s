%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MCK0Ysgce7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  345 ( 411 expanded)
%              Number of equality atoms :   40 (  49 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X27 @ X27 @ X28 @ X29 )
      = ( k1_enumset1 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k3_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_enumset1 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
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

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X4 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MCK0Ysgce7
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 84 iterations in 0.050s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(t13_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.51         ( k1_tarski @ A ) ) =>
% 0.20/0.51       ( ( A ) = ( B ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.51            ( k1_tarski @ A ) ) =>
% 0.20/0.51          ( ( A ) = ( B ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51         = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t69_enumset1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.51  thf('1', plain, (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf(t71_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X27 @ X27 @ X28 @ X29)
% 0.20/0.51           = (k1_enumset1 @ X27 @ X28 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.51  thf(t70_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t50_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.51     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.51       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.20/0.51           = (k2_xboole_0 @ (k2_enumset1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.20/0.51              (k1_tarski @ X23)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.20/0.51           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['1', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t72_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33)
% 0.20/0.51           = (k2_enumset1 @ X30 @ X31 @ X32 @ X33))),
% 0.20/0.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_tarski @ X0 @ X1)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.51  thf('12', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf(d1_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_2, axiom,
% 0.20/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.51          | (r2_hidden @ X7 @ X11)
% 0.20/0.51          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.20/0.51          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.20/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['13', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (((X3) != (X4)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X4 @ X4 @ X5 @ X2)),
% 0.20/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.51  thf('20', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['12', '19'])).
% 0.20/0.51  thf(d1_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X17 @ X16)
% 0.20/0.51          | ((X17) = (X14))
% 0.20/0.51          | ((X16) != (k1_tarski @ X14)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X14 : $i, X17 : $i]:
% 0.20/0.51         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain, (((sk_B) = (sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.51  thf('24', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
