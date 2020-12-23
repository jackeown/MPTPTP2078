%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UIr2u5j8gF

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:01 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   57 (  62 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  395 ( 443 expanded)
%              Number of equality atoms :   47 (  56 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ B @ C @ A ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X12 @ X10 @ X11 @ X9 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_enumset1])).

thf(t89_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X32 @ X32 @ X32 @ X33 @ X34 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t89_enumset1])).

thf(t80_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X24 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t80_enumset1])).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X32 @ X33 @ X34 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X6 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('19',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['4','22'])).

thf('24',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X3: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( X7 = X6 )
      | ( X7 = X3 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('26',plain,(
    ! [X3: $i,X6: $i,X7: $i] :
      ( ( X7 = X3 )
      | ( X7 = X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UIr2u5j8gF
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.60  % Solved by: fo/fo7.sh
% 0.43/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.60  % done 232 iterations in 0.130s
% 0.43/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.60  % SZS output start Refutation
% 0.43/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.60  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.43/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.60  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.43/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.60  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.43/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(t21_zfmisc_1, conjecture,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.43/0.60         ( k1_xboole_0 ) ) =>
% 0.43/0.60       ( ( A ) = ( B ) ) ))).
% 0.43/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.60    (~( ![A:$i,B:$i]:
% 0.43/0.60        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.43/0.60            ( k1_xboole_0 ) ) =>
% 0.43/0.60          ( ( A ) = ( B ) ) ) )),
% 0.43/0.60    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.43/0.60  thf('0', plain,
% 0.43/0.60      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(t98_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.43/0.60  thf('1', plain,
% 0.43/0.60      (![X1 : $i, X2 : $i]:
% 0.43/0.60         ((k2_xboole_0 @ X1 @ X2)
% 0.43/0.60           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.43/0.60  thf('2', plain,
% 0.43/0.60      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.43/0.60         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.43/0.60      inference('sup+', [status(thm)], ['0', '1'])).
% 0.43/0.60  thf(t5_boole, axiom,
% 0.43/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.60  thf('3', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.60  thf('4', plain,
% 0.43/0.60      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.43/0.60         = (k1_tarski @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.60  thf(t70_enumset1, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.43/0.60  thf('5', plain,
% 0.43/0.60      (![X18 : $i, X19 : $i]:
% 0.43/0.60         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.43/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.60  thf(t69_enumset1, axiom,
% 0.43/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.60  thf('6', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.43/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.60  thf('7', plain,
% 0.43/0.60      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.43/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.43/0.60  thf(t44_enumset1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.43/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.43/0.60  thf('8', plain,
% 0.43/0.60      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.60         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.43/0.60           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.43/0.60  thf('9', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 0.43/0.60           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.43/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.43/0.60  thf(t123_enumset1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ))).
% 0.43/0.60  thf('10', plain,
% 0.43/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.60         ((k2_enumset1 @ X12 @ X10 @ X11 @ X9)
% 0.43/0.60           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.43/0.60      inference('cnf', [status(esa)], [t123_enumset1])).
% 0.43/0.60  thf(t89_enumset1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ B @ C ) =
% 0.43/0.60       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.43/0.60  thf('11', plain,
% 0.43/0.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.43/0.60         ((k5_enumset1 @ X32 @ X32 @ X32 @ X32 @ X32 @ X33 @ X34)
% 0.43/0.60           = (k1_enumset1 @ X32 @ X33 @ X34))),
% 0.43/0.60      inference('cnf', [status(esa)], [t89_enumset1])).
% 0.43/0.60  thf(t80_enumset1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.43/0.60     ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E ) =
% 0.43/0.60       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.43/0.60  thf('12', plain,
% 0.43/0.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.43/0.60         ((k5_enumset1 @ X24 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.43/0.60           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.43/0.60      inference('cnf', [status(esa)], [t80_enumset1])).
% 0.43/0.60  thf('13', plain,
% 0.43/0.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.43/0.60         ((k3_enumset1 @ X32 @ X32 @ X32 @ X33 @ X34)
% 0.43/0.60           = (k1_enumset1 @ X32 @ X33 @ X34))),
% 0.43/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.43/0.60  thf('14', plain,
% 0.43/0.60      (![X18 : $i, X19 : $i]:
% 0.43/0.60         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.43/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.60  thf('15', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.43/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.43/0.60  thf(t72_enumset1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.43/0.60  thf('16', plain,
% 0.43/0.60      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.43/0.60         ((k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23)
% 0.43/0.60           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 0.43/0.60      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.60  thf('17', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 0.43/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.43/0.60  thf(d2_tarski, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.43/0.60       ( ![D:$i]:
% 0.43/0.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.43/0.60  thf('18', plain,
% 0.43/0.60      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.60         (((X4) != (X6))
% 0.43/0.60          | (r2_hidden @ X4 @ X5)
% 0.43/0.60          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.43/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.43/0.60  thf('19', plain,
% 0.43/0.60      (![X3 : $i, X6 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X6 @ X3))),
% 0.43/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.43/0.60  thf('20', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (r2_hidden @ X1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 0.43/0.60      inference('sup+', [status(thm)], ['17', '19'])).
% 0.43/0.60  thf('21', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (r2_hidden @ X0 @ (k2_enumset1 @ X1 @ X0 @ X0 @ X0))),
% 0.43/0.60      inference('sup+', [status(thm)], ['10', '20'])).
% 0.43/0.60  thf('22', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.43/0.60      inference('sup+', [status(thm)], ['9', '21'])).
% 0.43/0.60  thf('23', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.43/0.60      inference('sup+', [status(thm)], ['4', '22'])).
% 0.43/0.60  thf('24', plain,
% 0.43/0.60      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.43/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.60  thf('25', plain,
% 0.43/0.60      (![X3 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X7 @ X5)
% 0.43/0.60          | ((X7) = (X6))
% 0.43/0.60          | ((X7) = (X3))
% 0.43/0.60          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.43/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.43/0.60  thf('26', plain,
% 0.43/0.60      (![X3 : $i, X6 : $i, X7 : $i]:
% 0.43/0.60         (((X7) = (X3))
% 0.43/0.60          | ((X7) = (X6))
% 0.43/0.60          | ~ (r2_hidden @ X7 @ (k2_tarski @ X6 @ X3)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.43/0.60  thf('27', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['24', '26'])).
% 0.43/0.60  thf('28', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.43/0.60  thf('29', plain, (((sk_A) = (sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['23', '28'])).
% 0.43/0.60  thf('30', plain, (((sk_A) != (sk_B))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('31', plain, ($false),
% 0.43/0.60      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
