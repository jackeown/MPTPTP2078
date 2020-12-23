%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VnYk4drXuW

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  56 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  339 ( 376 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

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

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X7 ) )
      | ( r2_hidden @ X4 @ X7 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['21','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VnYk4drXuW
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 209 iterations in 0.121s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(t45_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.21/0.57       ( r2_hidden @ A @ B ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.21/0.57          ( r2_hidden @ A @ B ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.21/0.57  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t98_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ X12 @ X13)
% 0.21/0.57           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.57  thf(t71_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 0.21/0.57           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.57  thf(t70_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X27 : $i, X28 : $i]:
% 0.21/0.57         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.21/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.57  thf(t69_enumset1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.57  thf('5', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 0.21/0.57           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.57  thf(d1_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.57       ( ![E:$i]:
% 0.21/0.57         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.57           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_2, axiom,
% 0.21/0.57    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.57       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_3, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.57       ( ![E:$i]:
% 0.21/0.57         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.21/0.57          | (r2_hidden @ X19 @ X23)
% 0.21/0.57          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.57         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.21/0.57          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.21/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.57         ((r2_hidden @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.21/0.57          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2))),
% 0.21/0.57      inference('sup+', [status(thm)], ['7', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.57          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['6', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.21/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.57  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.57  thf(t1_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.57       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.57         ((r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X7))
% 0.21/0.57          | (r2_hidden @ X4 @ X7)
% 0.21/0.57          | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r2_hidden @ X0 @ X1)
% 0.21/0.57          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.21/0.57          | (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['1', '16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.57          | (r2_hidden @ X0 @ X2)
% 0.21/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r2_hidden @ X0 @ sk_B)
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.21/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.57  thf(t36_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.21/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.57          | (r2_hidden @ X0 @ X2)
% 0.21/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('25', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.57      inference('clc', [status(thm)], ['21', '24'])).
% 0.21/0.57  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
