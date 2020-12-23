%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UM51roNwgM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:26 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 145 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  445 (1096 expanded)
%              Number of equality atoms :   37 (  93 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_C
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X31 @ X30 @ X29 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['7','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UM51roNwgM
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.56/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.76  % Solved by: fo/fo7.sh
% 0.56/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.76  % done 589 iterations in 0.304s
% 0.56/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.76  % SZS output start Refutation
% 0.56/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.56/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.56/0.76  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.56/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.56/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.76  thf(t47_zfmisc_1, conjecture,
% 0.56/0.76    (![A:$i,B:$i,C:$i]:
% 0.56/0.76     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.56/0.76       ( r2_hidden @ A @ C ) ))).
% 0.56/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.76        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.56/0.76          ( r2_hidden @ A @ C ) ) )),
% 0.56/0.76    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.56/0.76  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf(t70_enumset1, axiom,
% 0.56/0.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.56/0.76  thf('1', plain,
% 0.56/0.76      (![X36 : $i, X37 : $i]:
% 0.56/0.76         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.56/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.76  thf(d1_enumset1, axiom,
% 0.56/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.56/0.76       ( ![E:$i]:
% 0.56/0.76         ( ( r2_hidden @ E @ D ) <=>
% 0.56/0.76           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.56/0.76  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.56/0.76  thf(zf_stmt_2, axiom,
% 0.56/0.76    (![E:$i,C:$i,B:$i,A:$i]:
% 0.56/0.76     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.56/0.76       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.56/0.76  thf(zf_stmt_3, axiom,
% 0.56/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.56/0.76       ( ![E:$i]:
% 0.56/0.76         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.56/0.76  thf('2', plain,
% 0.56/0.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.56/0.76         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.56/0.76          | (r2_hidden @ X18 @ X22)
% 0.56/0.76          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.56/0.76  thf('3', plain,
% 0.56/0.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.76         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.56/0.76          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.56/0.76      inference('simplify', [status(thm)], ['2'])).
% 0.56/0.76  thf('4', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.76         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.56/0.76          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.56/0.76      inference('sup+', [status(thm)], ['1', '3'])).
% 0.56/0.76  thf('5', plain,
% 0.56/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.56/0.76         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.56/0.76  thf('6', plain,
% 0.56/0.76      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.56/0.76         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.56/0.76      inference('simplify', [status(thm)], ['5'])).
% 0.56/0.76  thf('7', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.56/0.76      inference('sup-', [status(thm)], ['4', '6'])).
% 0.56/0.76  thf('8', plain,
% 0.56/0.76      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf(d10_xboole_0, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.56/0.76  thf('9', plain,
% 0.56/0.76      (![X6 : $i, X8 : $i]:
% 0.56/0.76         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.56/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.56/0.76  thf('10', plain,
% 0.56/0.76      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.56/0.76        | ((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.56/0.76  thf(t102_enumset1, axiom,
% 0.56/0.76    (![A:$i,B:$i,C:$i]:
% 0.56/0.76     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.56/0.76  thf('11', plain,
% 0.56/0.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.56/0.76         ((k1_enumset1 @ X31 @ X30 @ X29) = (k1_enumset1 @ X29 @ X30 @ X31))),
% 0.56/0.76      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.56/0.76  thf('12', plain,
% 0.56/0.76      (![X36 : $i, X37 : $i]:
% 0.56/0.76         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.56/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.76  thf('13', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]:
% 0.56/0.76         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.56/0.76      inference('sup+', [status(thm)], ['11', '12'])).
% 0.56/0.76  thf(t43_enumset1, axiom,
% 0.56/0.76    (![A:$i,B:$i,C:$i]:
% 0.56/0.76     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.56/0.76       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.56/0.76  thf('14', plain,
% 0.56/0.76      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.56/0.76         ((k1_enumset1 @ X32 @ X33 @ X34)
% 0.56/0.76           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ (k1_tarski @ X34)))),
% 0.56/0.76      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.56/0.76  thf(t7_xboole_1, axiom,
% 0.56/0.76    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.56/0.76  thf('15', plain,
% 0.56/0.76      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.56/0.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.56/0.76  thf('16', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.76         (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.56/0.76      inference('sup+', [status(thm)], ['14', '15'])).
% 0.56/0.76  thf('17', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]:
% 0.56/0.76         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.56/0.76      inference('sup+', [status(thm)], ['13', '16'])).
% 0.56/0.76  thf('18', plain,
% 0.56/0.76      (![X6 : $i, X8 : $i]:
% 0.56/0.76         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.56/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.56/0.76  thf('19', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]:
% 0.56/0.76         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 0.56/0.76          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.76  thf('20', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]:
% 0.56/0.76         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.56/0.76      inference('sup+', [status(thm)], ['13', '16'])).
% 0.56/0.76  thf('21', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.56/0.76      inference('demod', [status(thm)], ['19', '20'])).
% 0.56/0.76  thf(l51_zfmisc_1, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.56/0.76  thf('22', plain,
% 0.56/0.76      (![X47 : $i, X48 : $i]:
% 0.56/0.76         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.56/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.56/0.76  thf('23', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]:
% 0.56/0.76         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.76      inference('sup+', [status(thm)], ['21', '22'])).
% 0.56/0.76  thf('24', plain,
% 0.56/0.76      (![X47 : $i, X48 : $i]:
% 0.56/0.76         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.56/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.56/0.76  thf('25', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.76      inference('sup+', [status(thm)], ['23', '24'])).
% 0.56/0.76  thf('26', plain,
% 0.56/0.76      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.56/0.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.56/0.76  thf('27', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.76      inference('sup+', [status(thm)], ['23', '24'])).
% 0.56/0.76  thf('28', plain,
% 0.56/0.76      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.56/0.76      inference('demod', [status(thm)], ['10', '25', '26', '27'])).
% 0.56/0.76  thf('29', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.76      inference('sup+', [status(thm)], ['23', '24'])).
% 0.56/0.76  thf('30', plain,
% 0.56/0.76      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.56/0.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.56/0.76  thf('31', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.56/0.76      inference('sup+', [status(thm)], ['29', '30'])).
% 0.56/0.76  thf('32', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.56/0.76      inference('sup+', [status(thm)], ['28', '31'])).
% 0.56/0.76  thf(t28_xboole_1, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.56/0.76  thf('33', plain,
% 0.56/0.76      (![X9 : $i, X10 : $i]:
% 0.56/0.76         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.56/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.56/0.76  thf('34', plain,
% 0.56/0.76      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.56/0.76         = (k2_tarski @ sk_A @ sk_B))),
% 0.56/0.76      inference('sup-', [status(thm)], ['32', '33'])).
% 0.56/0.76  thf(d4_xboole_0, axiom,
% 0.56/0.76    (![A:$i,B:$i,C:$i]:
% 0.56/0.76     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.56/0.76       ( ![D:$i]:
% 0.56/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.56/0.76           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.56/0.76  thf('35', plain,
% 0.56/0.76      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.56/0.76         (~ (r2_hidden @ X4 @ X3)
% 0.56/0.76          | (r2_hidden @ X4 @ X2)
% 0.56/0.76          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.56/0.76      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.56/0.76  thf('36', plain,
% 0.56/0.76      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.56/0.76         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.56/0.76      inference('simplify', [status(thm)], ['35'])).
% 0.56/0.76  thf('37', plain,
% 0.56/0.76      (![X0 : $i]:
% 0.56/0.76         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.56/0.76          | (r2_hidden @ X0 @ sk_C))),
% 0.56/0.76      inference('sup-', [status(thm)], ['34', '36'])).
% 0.56/0.76  thf('38', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.56/0.76      inference('sup-', [status(thm)], ['7', '37'])).
% 0.56/0.76  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.56/0.76  
% 0.56/0.76  % SZS output end Refutation
% 0.56/0.76  
% 0.61/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
