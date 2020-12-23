%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3V8h7pLbyn

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:38 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  338 ( 366 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t75_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) ),
    inference('cnf.neg',[status(esa)],[t75_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k2_xboole_0 @ X9 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3V8h7pLbyn
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.21/1.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.21/1.44  % Solved by: fo/fo7.sh
% 1.21/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.44  % done 942 iterations in 1.030s
% 1.21/1.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.21/1.44  % SZS output start Refutation
% 1.21/1.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.44  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.21/1.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.21/1.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.21/1.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.21/1.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.21/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.44  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.21/1.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.21/1.44  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.21/1.44                                           $i > $i).
% 1.21/1.44  thf(sk_F_type, type, sk_F: $i).
% 1.21/1.44  thf(sk_G_type, type, sk_G: $i).
% 1.21/1.44  thf(sk_E_type, type, sk_E: $i).
% 1.21/1.44  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.21/1.44  thf(t75_enumset1, conjecture,
% 1.21/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.21/1.44     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.21/1.44       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.21/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.44    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.21/1.44        ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.21/1.44          ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )),
% 1.21/1.44    inference('cnf.neg', [status(esa)], [t75_enumset1])).
% 1.21/1.44  thf('0', plain,
% 1.21/1.44      (((k6_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F @ 
% 1.21/1.44         sk_G)
% 1.21/1.44         != (k5_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F @ sk_G))),
% 1.21/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.44  thf(t56_enumset1, axiom,
% 1.21/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.21/1.44     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 1.21/1.44       ( k2_xboole_0 @
% 1.21/1.44         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 1.21/1.44  thf('1', plain,
% 1.21/1.44      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.21/1.44         ((k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.21/1.44           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 1.21/1.44              (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)))),
% 1.21/1.44      inference('cnf', [status(esa)], [t56_enumset1])).
% 1.21/1.44  thf(commutativity_k2_xboole_0, axiom,
% 1.21/1.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.21/1.44  thf('2', plain,
% 1.21/1.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.21/1.44  thf(d3_tarski, axiom,
% 1.21/1.44    (![A:$i,B:$i]:
% 1.21/1.44     ( ( r1_tarski @ A @ B ) <=>
% 1.21/1.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.21/1.44  thf('3', plain,
% 1.21/1.44      (![X3 : $i, X5 : $i]:
% 1.21/1.44         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.21/1.44      inference('cnf', [status(esa)], [d3_tarski])).
% 1.21/1.44  thf(d3_xboole_0, axiom,
% 1.21/1.44    (![A:$i,B:$i,C:$i]:
% 1.21/1.44     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.21/1.44       ( ![D:$i]:
% 1.21/1.44         ( ( r2_hidden @ D @ C ) <=>
% 1.21/1.44           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.21/1.44  thf('4', plain,
% 1.21/1.44      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.21/1.44         (~ (r2_hidden @ X6 @ X7)
% 1.21/1.44          | (r2_hidden @ X6 @ X8)
% 1.21/1.44          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 1.21/1.44      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.21/1.44  thf('5', plain,
% 1.21/1.44      (![X6 : $i, X7 : $i, X9 : $i]:
% 1.21/1.44         ((r2_hidden @ X6 @ (k2_xboole_0 @ X9 @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 1.21/1.44      inference('simplify', [status(thm)], ['4'])).
% 1.21/1.44  thf('6', plain,
% 1.21/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.44         ((r1_tarski @ X0 @ X1)
% 1.21/1.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 1.21/1.44      inference('sup-', [status(thm)], ['3', '5'])).
% 1.21/1.44  thf('7', plain,
% 1.21/1.44      (![X3 : $i, X5 : $i]:
% 1.21/1.44         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.21/1.44      inference('cnf', [status(esa)], [d3_tarski])).
% 1.21/1.44  thf('8', plain,
% 1.21/1.44      (![X0 : $i, X1 : $i]:
% 1.21/1.44         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.44          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.21/1.44      inference('sup-', [status(thm)], ['6', '7'])).
% 1.21/1.44  thf('9', plain,
% 1.21/1.44      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.21/1.44      inference('simplify', [status(thm)], ['8'])).
% 1.21/1.44  thf('10', plain,
% 1.21/1.44      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.21/1.44      inference('sup+', [status(thm)], ['2', '9'])).
% 1.21/1.44  thf(t12_xboole_1, axiom,
% 1.21/1.44    (![A:$i,B:$i]:
% 1.21/1.44     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.21/1.44  thf('11', plain,
% 1.21/1.44      (![X12 : $i, X13 : $i]:
% 1.21/1.44         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.21/1.44      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.21/1.44  thf('12', plain,
% 1.21/1.44      (![X0 : $i, X1 : $i]:
% 1.21/1.44         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.44           = (k2_xboole_0 @ X1 @ X0))),
% 1.21/1.44      inference('sup-', [status(thm)], ['10', '11'])).
% 1.21/1.44  thf('13', plain,
% 1.21/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.21/1.44         ((k2_xboole_0 @ (k1_tarski @ X6) @ 
% 1.21/1.44           (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.21/1.44           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 1.21/1.44              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 1.21/1.44      inference('sup+', [status(thm)], ['1', '12'])).
% 1.21/1.44  thf(t62_enumset1, axiom,
% 1.21/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.21/1.44     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.21/1.44       ( k2_xboole_0 @
% 1.21/1.44         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 1.21/1.44  thf('14', plain,
% 1.21/1.44      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, 
% 1.21/1.44         X28 : $i]:
% 1.21/1.44         ((k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 1.21/1.44           = (k2_xboole_0 @ (k1_tarski @ X21) @ 
% 1.21/1.44              (k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)))),
% 1.21/1.44      inference('cnf', [status(esa)], [t62_enumset1])).
% 1.21/1.44  thf('15', plain,
% 1.21/1.44      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.21/1.44         ((k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.21/1.44           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 1.21/1.44              (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)))),
% 1.21/1.44      inference('cnf', [status(esa)], [t56_enumset1])).
% 1.21/1.44  thf('16', plain,
% 1.21/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.21/1.44         ((k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.21/1.44           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.21/1.44      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.21/1.44  thf('17', plain,
% 1.21/1.44      (((k5_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F @ sk_G)
% 1.21/1.44         != (k5_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F @ sk_G))),
% 1.21/1.44      inference('demod', [status(thm)], ['0', '16'])).
% 1.21/1.44  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 1.21/1.44  
% 1.21/1.44  % SZS output end Refutation
% 1.21/1.44  
% 1.21/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
