%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2nSAuDd3FC

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:54 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   57 (  62 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  373 ( 416 expanded)
%              Number of equality atoms :   47 (  54 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X31 @ X32 @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X13 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( X26 = X23 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2nSAuDd3FC
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.80  % Solved by: fo/fo7.sh
% 0.61/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.80  % done 496 iterations in 0.349s
% 0.61/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.80  % SZS output start Refutation
% 0.61/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.61/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.61/0.80  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.61/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(t21_zfmisc_1, conjecture,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.61/0.80         ( k1_xboole_0 ) ) =>
% 0.61/0.80       ( ( A ) = ( B ) ) ))).
% 0.61/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.80    (~( ![A:$i,B:$i]:
% 0.61/0.80        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.61/0.80            ( k1_xboole_0 ) ) =>
% 0.61/0.80          ( ( A ) = ( B ) ) ) )),
% 0.61/0.80    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.61/0.80  thf('0', plain,
% 0.61/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(t98_xboole_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.61/0.80  thf('1', plain,
% 0.61/0.80      (![X9 : $i, X10 : $i]:
% 0.61/0.80         ((k2_xboole_0 @ X9 @ X10)
% 0.61/0.80           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.61/0.80  thf('2', plain,
% 0.61/0.80      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.61/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['0', '1'])).
% 0.61/0.80  thf(commutativity_k5_xboole_0, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.61/0.80  thf('3', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.80  thf('4', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.80  thf(t5_boole, axiom,
% 0.61/0.80    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.80  thf('5', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.61/0.80      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.80  thf('6', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['4', '5'])).
% 0.61/0.80  thf('7', plain,
% 0.61/0.80      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.61/0.80         = (k1_tarski @ sk_B))),
% 0.61/0.80      inference('demod', [status(thm)], ['2', '3', '6'])).
% 0.61/0.80  thf(t69_enumset1, axiom,
% 0.61/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.61/0.80  thf('8', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.61/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.80  thf(t70_enumset1, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.61/0.80  thf('9', plain,
% 0.61/0.80      (![X36 : $i, X37 : $i]:
% 0.61/0.80         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.61/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.61/0.80  thf(t46_enumset1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.61/0.80       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.61/0.80  thf('10', plain,
% 0.61/0.80      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X31 @ X32 @ X33 @ X34)
% 0.61/0.80           = (k2_xboole_0 @ (k1_enumset1 @ X31 @ X32 @ X33) @ (k1_tarski @ X34)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.61/0.80  thf('11', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.61/0.80           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.61/0.80  thf('12', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.61/0.80           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['8', '11'])).
% 0.61/0.80  thf(t71_enumset1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.61/0.80  thf('13', plain,
% 0.61/0.80      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 0.61/0.80           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.61/0.80  thf('14', plain,
% 0.61/0.80      (![X36 : $i, X37 : $i]:
% 0.61/0.80         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.61/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.61/0.80  thf('15', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['13', '14'])).
% 0.61/0.80  thf('16', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_tarski @ X0 @ X1)
% 0.61/0.80           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.61/0.80      inference('demod', [status(thm)], ['12', '15'])).
% 0.61/0.80  thf('17', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.61/0.80      inference('demod', [status(thm)], ['7', '16'])).
% 0.61/0.80  thf('18', plain,
% 0.61/0.80      (![X36 : $i, X37 : $i]:
% 0.61/0.80         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.61/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.61/0.80  thf(d1_enumset1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.61/0.80       ( ![E:$i]:
% 0.61/0.80         ( ( r2_hidden @ E @ D ) <=>
% 0.61/0.80           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.61/0.80  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.61/0.80  thf(zf_stmt_2, axiom,
% 0.61/0.80    (![E:$i,C:$i,B:$i,A:$i]:
% 0.61/0.80     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.61/0.80       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.61/0.80  thf(zf_stmt_3, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.61/0.80       ( ![E:$i]:
% 0.61/0.80         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.61/0.80  thf('19', plain,
% 0.61/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.80         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.61/0.80          | (r2_hidden @ X16 @ X20)
% 0.61/0.80          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.80  thf('20', plain,
% 0.61/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.61/0.80         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.61/0.80          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.61/0.80      inference('simplify', [status(thm)], ['19'])).
% 0.61/0.80  thf('21', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.61/0.80          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.61/0.80      inference('sup+', [status(thm)], ['18', '20'])).
% 0.61/0.80  thf('22', plain,
% 0.61/0.80      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.80         (((X12) != (X13)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.80  thf('23', plain,
% 0.61/0.80      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.61/0.80         ~ (zip_tseitin_0 @ X13 @ X13 @ X14 @ X11)),
% 0.61/0.80      inference('simplify', [status(thm)], ['22'])).
% 0.61/0.80  thf('24', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.61/0.80      inference('sup-', [status(thm)], ['21', '23'])).
% 0.61/0.80  thf('25', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.61/0.80      inference('sup+', [status(thm)], ['17', '24'])).
% 0.61/0.80  thf(d1_tarski, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.61/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.61/0.80  thf('26', plain,
% 0.61/0.80      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X26 @ X25)
% 0.61/0.80          | ((X26) = (X23))
% 0.61/0.80          | ((X25) != (k1_tarski @ X23)))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_tarski])).
% 0.61/0.80  thf('27', plain,
% 0.61/0.80      (![X23 : $i, X26 : $i]:
% 0.61/0.80         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 0.61/0.80      inference('simplify', [status(thm)], ['26'])).
% 0.61/0.80  thf('28', plain, (((sk_A) = (sk_B))),
% 0.61/0.80      inference('sup-', [status(thm)], ['25', '27'])).
% 0.61/0.80  thf('29', plain, (((sk_A) != (sk_B))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('30', plain, ($false),
% 0.61/0.80      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.61/0.80  
% 0.61/0.80  % SZS output end Refutation
% 0.61/0.80  
% 0.61/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
