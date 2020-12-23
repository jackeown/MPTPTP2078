%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VRSn3mIWqG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  66 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  398 ( 428 expanded)
%              Number of equality atoms :   46 (  49 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X27 )
      | ( r2_hidden @ X25 @ X26 )
      | ( X26
       != ( k2_tarski @ X27 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X24: $i,X27: $i] :
      ( r2_hidden @ X27 @ ( k2_tarski @ X27 @ X24 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( X22 = X19 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22 = X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k2_tarski @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VRSn3mIWqG
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 196 iterations in 0.118s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(t70_enumset1, conjecture,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d2_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.54         (((X25) != (X27))
% 0.21/0.54          | (r2_hidden @ X25 @ X26)
% 0.21/0.54          | ((X26) != (k2_tarski @ X27 @ X24)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X24 : $i, X27 : $i]: (r2_hidden @ X27 @ (k2_tarski @ X27 @ X24))),
% 0.21/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.54  thf(d3_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X5 : $i, X7 : $i]:
% 0.21/0.54         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.54  thf(d1_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X22 @ X21)
% 0.21/0.54          | ((X22) = (X19))
% 0.21/0.54          | ((X21) != (k1_tarski @ X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X19 : $i, X22 : $i]:
% 0.21/0.54         (((X22) = (X19)) | ~ (r2_hidden @ X22 @ (k1_tarski @ X19)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.54          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X5 : $i, X7 : $i]:
% 0.21/0.54         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.54          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.54          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.54  thf(t28_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.21/0.54           = (k1_tarski @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.54  thf(t100_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X8 @ X9)
% 0.21/0.54           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf(commutativity_k5_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.54  thf(t92_xboole_1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('17', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.54  thf(t91_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.54       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.54         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.21/0.54           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.54  thf(t5_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.54  thf('21', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.54  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['16', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((X1)
% 0.21/0.54           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['15', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((X1)
% 0.21/0.54           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_tarski @ X0 @ X1)
% 0.21/0.54           = (k5_xboole_0 @ 
% 0.21/0.54              (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)) @ 
% 0.21/0.54              (k1_tarski @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['12', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.54  thf(t98_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X17 @ X18)
% 0.21/0.54           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.54  thf(t42_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.54         ((k1_enumset1 @ X30 @ X31 @ X32)
% 0.21/0.54           = (k2_xboole_0 @ (k1_tarski @ X30) @ (k2_tarski @ X31 @ X32)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.54  thf('33', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '32'])).
% 0.21/0.54  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
