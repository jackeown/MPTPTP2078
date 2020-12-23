%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cMocFvP9sr

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:10 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 ( 330 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','19'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cMocFvP9sr
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 266 iterations in 0.105s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.56  thf(t46_zfmisc_1, conjecture,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.56       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i,B:$i]:
% 0.39/0.56        ( ( r2_hidden @ A @ B ) =>
% 0.39/0.56          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.39/0.56  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(d10_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.56  thf('2', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.39/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.56  thf(l1_zfmisc_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X27 : $i, X28 : $i]:
% 0.39/0.56         ((r2_hidden @ X27 @ X28) | ~ (r1_tarski @ (k1_tarski @ X27) @ X28))),
% 0.39/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.56  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.56  thf(d4_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.39/0.56       ( ![D:$i]:
% 0.39/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X6 @ X7)
% 0.39/0.56          | ~ (r2_hidden @ X6 @ X8)
% 0.39/0.56          | (r2_hidden @ X6 @ X9)
% 0.39/0.56          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.56         ((r2_hidden @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 0.39/0.56          | ~ (r2_hidden @ X6 @ X8)
% 0.39/0.56          | ~ (r2_hidden @ X6 @ X7))),
% 0.39/0.56      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.56          | (r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['0', '7'])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X27 : $i, X29 : $i]:
% 0.39/0.56         ((r1_tarski @ (k1_tarski @ X27) @ X29) | ~ (r2_hidden @ X27 @ X29))),
% 0.39/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.39/0.56        (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X12 : $i, X14 : $i]:
% 0.39/0.56         (((X12) = (X14))
% 0.39/0.56          | ~ (r1_tarski @ X14 @ X12)
% 0.39/0.56          | ~ (r1_tarski @ X12 @ X14))),
% 0.39/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.56           (k1_tarski @ sk_A))
% 0.39/0.56        | ((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf(d3_tarski, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (![X3 : $i, X5 : $i]:
% 0.39/0.56         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X10 @ X9)
% 0.39/0.56          | (r2_hidden @ X10 @ X8)
% 0.39/0.56          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.39/0.56         ((r2_hidden @ X10 @ X8)
% 0.39/0.56          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.39/0.56          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '15'])).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (![X3 : $i, X5 : $i]:
% 0.39/0.56         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.56          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.39/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['12', '19'])).
% 0.39/0.56  thf(t22_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X15 : $i, X16 : $i]:
% 0.39/0.56         ((k2_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)) = (X15))),
% 0.39/0.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.39/0.56  thf('22', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.39/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.56  thf('23', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.56  thf('25', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.39/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.56  thf('26', plain, ($false),
% 0.39/0.56      inference('simplify_reflect-', [status(thm)], ['22', '25'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
