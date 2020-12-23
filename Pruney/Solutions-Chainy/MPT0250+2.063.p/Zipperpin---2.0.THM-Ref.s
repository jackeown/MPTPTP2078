%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X3k3FjRcT2

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:55 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 125 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  437 ( 991 expanded)
%              Number of equality atoms :   36 (  80 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('21',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','18','19','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
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

thf('24',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 )
      | ( r2_hidden @ X36 @ X40 )
      | ( X40
       != ( k1_enumset1 @ X39 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X36 @ ( k1_enumset1 @ X39 @ X38 @ X37 ) )
      | ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X32 != X31 )
      | ~ ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ~ ( zip_tseitin_0 @ X31 @ X33 @ X34 @ X31 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['21','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X3k3FjRcT2
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 665 iterations in 0.369s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.59/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.82  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.82  thf(t45_zfmisc_1, conjecture,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.59/0.82       ( r2_hidden @ A @ B ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i,B:$i]:
% 0.59/0.82        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.59/0.82          ( r2_hidden @ A @ B ) ) )),
% 0.59/0.82    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.59/0.82  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('1', plain,
% 0.59/0.82      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(d10_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.82  thf('2', plain,
% 0.59/0.82      (![X11 : $i, X13 : $i]:
% 0.59/0.82         (((X11) = (X13))
% 0.59/0.82          | ~ (r1_tarski @ X13 @ X11)
% 0.59/0.82          | ~ (r1_tarski @ X11 @ X13))),
% 0.59/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.82  thf('3', plain,
% 0.59/0.82      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.59/0.82        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.82  thf(commutativity_k5_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.59/0.82  thf('4', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.82  thf(t93_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( k2_xboole_0 @ A @ B ) =
% 0.59/0.82       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.82  thf('5', plain,
% 0.59/0.82      (![X27 : $i, X28 : $i]:
% 0.59/0.82         ((k2_xboole_0 @ X27 @ X28)
% 0.59/0.82           = (k2_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 0.59/0.82              (k3_xboole_0 @ X27 @ X28)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.59/0.82  thf('6', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((k2_xboole_0 @ X0 @ X1)
% 0.59/0.82           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['4', '5'])).
% 0.59/0.82  thf('7', plain,
% 0.59/0.82      (![X27 : $i, X28 : $i]:
% 0.59/0.82         ((k2_xboole_0 @ X27 @ X28)
% 0.59/0.82           = (k2_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 0.59/0.82              (k3_xboole_0 @ X27 @ X28)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.59/0.82  thf(t7_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.82  thf('8', plain,
% 0.59/0.82      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.59/0.82      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.82  thf('9', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.82      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.82  thf('10', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (r1_tarski @ 
% 0.59/0.82          (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.59/0.82          (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.82      inference('sup+', [status(thm)], ['6', '9'])).
% 0.59/0.82  thf(t91_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.82       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.82  thf('11', plain,
% 0.59/0.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 0.59/0.82           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.82  thf(t100_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.82  thf('12', plain,
% 0.59/0.82      (![X16 : $i, X17 : $i]:
% 0.59/0.82         ((k4_xboole_0 @ X16 @ X17)
% 0.59/0.82           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.82  thf(t98_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.59/0.82  thf('13', plain,
% 0.59/0.82      (![X29 : $i, X30 : $i]:
% 0.59/0.82         ((k2_xboole_0 @ X29 @ X30)
% 0.59/0.82           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.82  thf('14', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.82      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.59/0.82  thf('15', plain,
% 0.59/0.82      (![X11 : $i, X13 : $i]:
% 0.59/0.82         (((X11) = (X13))
% 0.59/0.82          | ~ (r1_tarski @ X13 @ X11)
% 0.59/0.82          | ~ (r1_tarski @ X11 @ X13))),
% 0.59/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.82  thf('16', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.59/0.82          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.82  thf('17', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.82      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.59/0.82  thf('18', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('demod', [status(thm)], ['16', '17'])).
% 0.59/0.82  thf('19', plain,
% 0.59/0.82      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.59/0.82      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.82  thf('20', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('demod', [status(thm)], ['16', '17'])).
% 0.59/0.82  thf('21', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.59/0.82      inference('demod', [status(thm)], ['3', '18', '19', '20'])).
% 0.59/0.82  thf(t69_enumset1, axiom,
% 0.59/0.82    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.82  thf('22', plain,
% 0.59/0.82      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 0.59/0.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.82  thf(t70_enumset1, axiom,
% 0.59/0.82    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.82  thf('23', plain,
% 0.59/0.82      (![X44 : $i, X45 : $i]:
% 0.59/0.82         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 0.59/0.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.82  thf(d1_enumset1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.82     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.82       ( ![E:$i]:
% 0.59/0.82         ( ( r2_hidden @ E @ D ) <=>
% 0.59/0.82           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.59/0.82  thf(zf_stmt_2, axiom,
% 0.59/0.82    (![E:$i,C:$i,B:$i,A:$i]:
% 0.59/0.82     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.59/0.82       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_3, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.82     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.82       ( ![E:$i]:
% 0.59/0.82         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.59/0.82  thf('24', plain,
% 0.59/0.82      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.59/0.82         ((zip_tseitin_0 @ X36 @ X37 @ X38 @ X39)
% 0.59/0.82          | (r2_hidden @ X36 @ X40)
% 0.59/0.82          | ((X40) != (k1_enumset1 @ X39 @ X38 @ X37)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.82  thf('25', plain,
% 0.59/0.82      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.59/0.82         ((r2_hidden @ X36 @ (k1_enumset1 @ X39 @ X38 @ X37))
% 0.59/0.82          | (zip_tseitin_0 @ X36 @ X37 @ X38 @ X39))),
% 0.59/0.82      inference('simplify', [status(thm)], ['24'])).
% 0.59/0.82  thf('26', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.59/0.82          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.59/0.82      inference('sup+', [status(thm)], ['23', '25'])).
% 0.59/0.82  thf('27', plain,
% 0.59/0.82      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.82         (((X32) != (X31)) | ~ (zip_tseitin_0 @ X32 @ X33 @ X34 @ X31))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.82  thf('28', plain,
% 0.59/0.82      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.59/0.82         ~ (zip_tseitin_0 @ X31 @ X33 @ X34 @ X31)),
% 0.59/0.82      inference('simplify', [status(thm)], ['27'])).
% 0.59/0.82  thf('29', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.59/0.82      inference('sup-', [status(thm)], ['26', '28'])).
% 0.59/0.82  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.82      inference('sup+', [status(thm)], ['22', '29'])).
% 0.59/0.82  thf(d3_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.59/0.82       ( ![D:$i]:
% 0.59/0.82         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.82           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.82  thf('31', plain,
% 0.59/0.82      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X2 @ X3)
% 0.59/0.82          | (r2_hidden @ X2 @ X4)
% 0.59/0.82          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.59/0.82      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.59/0.82  thf('32', plain,
% 0.59/0.82      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.59/0.82         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.59/0.82      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.82  thf('33', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['30', '32'])).
% 0.59/0.82  thf('34', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.59/0.82      inference('sup+', [status(thm)], ['21', '33'])).
% 0.59/0.82  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.59/0.82  
% 0.59/0.82  % SZS output end Refutation
% 0.59/0.82  
% 0.66/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
