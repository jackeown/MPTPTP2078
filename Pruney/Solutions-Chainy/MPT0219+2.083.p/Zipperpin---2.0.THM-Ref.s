%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.11e88FMFuU

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:14 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   65 (  74 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  473 ( 567 expanded)
%              Number of equality atoms :   54 (  67 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( X23 = X24 )
      | ( X23 = X25 )
      | ( X23 = X26 ) ) ),
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

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['3','19'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
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

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X31 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) )
      | ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X22 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ~ ( zip_tseitin_0 @ X32 @ X28 @ X29 @ X30 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X28 @ X29 @ X30 )
      | ~ ( r2_hidden @ X32 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.11e88FMFuU
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 476 iterations in 0.712s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.99/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.99/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(d1_enumset1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.17     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.99/1.17       ( ![E:$i]:
% 0.99/1.17         ( ( r2_hidden @ E @ D ) <=>
% 0.99/1.17           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_0, axiom,
% 0.99/1.17    (![E:$i,C:$i,B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.99/1.17       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.99/1.17  thf('0', plain,
% 0.99/1.17      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.99/1.17         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 0.99/1.17          | ((X23) = (X24))
% 0.99/1.17          | ((X23) = (X25))
% 0.99/1.17          | ((X23) = (X26)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t13_zfmisc_1, conjecture,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.99/1.17         ( k1_tarski @ A ) ) =>
% 0.99/1.17       ( ( A ) = ( B ) ) ))).
% 0.99/1.17  thf(zf_stmt_1, negated_conjecture,
% 0.99/1.17    (~( ![A:$i,B:$i]:
% 0.99/1.17        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.99/1.17            ( k1_tarski @ A ) ) =>
% 0.99/1.17          ( ( A ) = ( B ) ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.99/1.17  thf('1', plain,
% 0.99/1.17      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.99/1.17         = (k1_tarski @ sk_A))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.17  thf(t41_enumset1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k2_tarski @ A @ B ) =
% 0.99/1.17       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.99/1.17  thf('2', plain,
% 0.99/1.17      (![X34 : $i, X35 : $i]:
% 0.99/1.17         ((k2_tarski @ X34 @ X35)
% 0.99/1.17           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X35)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.99/1.17  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['1', '2'])).
% 0.99/1.17  thf(t94_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k2_xboole_0 @ A @ B ) =
% 0.99/1.17       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.99/1.17  thf('4', plain,
% 0.99/1.17      (![X16 : $i, X17 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X16 @ X17)
% 0.99/1.17           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.99/1.17              (k3_xboole_0 @ X16 @ X17)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.99/1.17  thf(t91_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.99/1.17       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.17           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.99/1.17  thf('6', plain,
% 0.99/1.17      (![X16 : $i, X17 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X16 @ X17)
% 0.99/1.17           = (k5_xboole_0 @ X16 @ 
% 0.99/1.17              (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X16 @ X17))))),
% 0.99/1.17      inference('demod', [status(thm)], ['4', '5'])).
% 0.99/1.17  thf('7', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.17           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.99/1.17  thf(commutativity_k5_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.99/1.17           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['7', '8'])).
% 0.99/1.17  thf('10', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X1 @ X0)
% 0.99/1.17           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['6', '9'])).
% 0.99/1.17  thf('11', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.99/1.17  thf(t100_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.99/1.17  thf('12', plain,
% 0.99/1.17      (![X5 : $i, X6 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X5 @ X6)
% 0.99/1.17           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.99/1.17  thf('13', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X1 @ X0)
% 0.99/1.17           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.99/1.17  thf(t98_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.99/1.17  thf('14', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X20 @ X21)
% 0.99/1.17           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.99/1.17  thf('15', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['13', '14'])).
% 0.99/1.17  thf('16', plain,
% 0.99/1.17      (![X34 : $i, X35 : $i]:
% 0.99/1.17         ((k2_tarski @ X34 @ X35)
% 0.99/1.17           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X35)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k2_tarski @ X0 @ X1)
% 0.99/1.17           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['15', '16'])).
% 0.99/1.17  thf('18', plain,
% 0.99/1.17      (![X34 : $i, X35 : $i]:
% 0.99/1.17         ((k2_tarski @ X34 @ X35)
% 0.99/1.17           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X35)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.99/1.17  thf('19', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['17', '18'])).
% 0.99/1.17  thf('20', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['3', '19'])).
% 0.99/1.17  thf(t70_enumset1, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.99/1.17  thf('21', plain,
% 0.99/1.17      (![X43 : $i, X44 : $i]:
% 0.99/1.17         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 0.99/1.17      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.99/1.17  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_3, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.17     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.99/1.17       ( ![E:$i]:
% 0.99/1.17         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.99/1.17  thf('22', plain,
% 0.99/1.17      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.17         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 0.99/1.17          | (r2_hidden @ X27 @ X31)
% 0.99/1.17          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.17  thf('23', plain,
% 0.99/1.17      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.99/1.17         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 0.99/1.17          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 0.99/1.17      inference('simplify', [status(thm)], ['22'])).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.99/1.17          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.99/1.17      inference('sup+', [status(thm)], ['21', '23'])).
% 0.99/1.17  thf('25', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.99/1.17         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('26', plain,
% 0.99/1.17      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.99/1.17         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 0.99/1.17      inference('simplify', [status(thm)], ['25'])).
% 0.99/1.17  thf('27', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.99/1.17      inference('sup-', [status(thm)], ['24', '26'])).
% 0.99/1.17  thf('28', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.99/1.17      inference('sup+', [status(thm)], ['20', '27'])).
% 0.99/1.17  thf(t69_enumset1, axiom,
% 0.99/1.17    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.99/1.17  thf('29', plain,
% 0.99/1.17      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 0.99/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.99/1.17  thf('30', plain,
% 0.99/1.17      (![X43 : $i, X44 : $i]:
% 0.99/1.17         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 0.99/1.17      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.99/1.17  thf('31', plain,
% 0.99/1.17      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X32 @ X31)
% 0.99/1.17          | ~ (zip_tseitin_0 @ X32 @ X28 @ X29 @ X30)
% 0.99/1.17          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.17  thf('32', plain,
% 0.99/1.17      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i]:
% 0.99/1.17         (~ (zip_tseitin_0 @ X32 @ X28 @ X29 @ X30)
% 0.99/1.17          | ~ (r2_hidden @ X32 @ (k1_enumset1 @ X30 @ X29 @ X28)))),
% 0.99/1.17      inference('simplify', [status(thm)], ['31'])).
% 0.99/1.17  thf('33', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.99/1.17          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.99/1.17      inference('sup-', [status(thm)], ['30', '32'])).
% 0.99/1.17  thf('34', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.99/1.17          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['29', '33'])).
% 0.99/1.17  thf('35', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.99/1.17      inference('sup-', [status(thm)], ['28', '34'])).
% 0.99/1.17  thf('36', plain,
% 0.99/1.17      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '35'])).
% 0.99/1.17  thf('37', plain, (((sk_B) = (sk_A))),
% 0.99/1.17      inference('simplify', [status(thm)], ['36'])).
% 0.99/1.17  thf('38', plain, (((sk_A) != (sk_B))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.17  thf('39', plain, ($false),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 0.99/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
