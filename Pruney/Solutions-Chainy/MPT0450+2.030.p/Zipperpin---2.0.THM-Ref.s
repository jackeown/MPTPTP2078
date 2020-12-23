%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5wDxJ5rweT

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:05 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  311 ( 394 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k3_relat_1 @ X18 ) @ ( k3_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k3_relat_1 @ X18 ) @ ( k3_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( r1_tarski @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5wDxJ5rweT
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.64  % Solved by: fo/fo7.sh
% 0.44/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.64  % done 192 iterations in 0.183s
% 0.44/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.64  % SZS output start Refutation
% 0.44/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.64  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.44/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.64  thf(fc1_relat_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.64  thf('0', plain,
% 0.44/0.64      (![X15 : $i, X16 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.44/0.64  thf(d3_tarski, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.64  thf('1', plain,
% 0.44/0.64      (![X1 : $i, X3 : $i]:
% 0.44/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.64  thf(d4_xboole_0, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.44/0.64       ( ![D:$i]:
% 0.44/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.64           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.44/0.64  thf('2', plain,
% 0.44/0.64      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X8 @ X7)
% 0.44/0.64          | (r2_hidden @ X8 @ X6)
% 0.44/0.64          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.44/0.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.44/0.64  thf('3', plain,
% 0.44/0.64      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.44/0.64         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['2'])).
% 0.44/0.64  thf('4', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.44/0.64          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['1', '3'])).
% 0.44/0.64  thf('5', plain,
% 0.44/0.64      (![X1 : $i, X3 : $i]:
% 0.44/0.64         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.64  thf('6', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.44/0.64          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.64  thf('7', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.44/0.64      inference('simplify', [status(thm)], ['6'])).
% 0.44/0.64  thf(t31_relat_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ A ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( v1_relat_1 @ B ) =>
% 0.44/0.64           ( ( r1_tarski @ A @ B ) =>
% 0.44/0.64             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.44/0.64  thf('8', plain,
% 0.44/0.64      (![X17 : $i, X18 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X17)
% 0.44/0.64          | (r1_tarski @ (k3_relat_1 @ X18) @ (k3_relat_1 @ X17))
% 0.44/0.64          | ~ (r1_tarski @ X18 @ X17)
% 0.44/0.64          | ~ (v1_relat_1 @ X18))),
% 0.44/0.64      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.44/0.64  thf('9', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.64          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.44/0.64             (k3_relat_1 @ X0))
% 0.44/0.64          | ~ (v1_relat_1 @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.64  thf('10', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X1)
% 0.44/0.64          | ~ (v1_relat_1 @ X0)
% 0.44/0.64          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.44/0.64             (k3_relat_1 @ X0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['0', '9'])).
% 0.44/0.64  thf(t17_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.64  thf('11', plain,
% 0.44/0.64      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.44/0.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.44/0.64  thf('12', plain,
% 0.44/0.64      (![X17 : $i, X18 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X17)
% 0.44/0.64          | (r1_tarski @ (k3_relat_1 @ X18) @ (k3_relat_1 @ X17))
% 0.44/0.64          | ~ (r1_tarski @ X18 @ X17)
% 0.44/0.64          | ~ (v1_relat_1 @ X18))),
% 0.44/0.64      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.44/0.64  thf('13', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.44/0.64          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.44/0.64             (k3_relat_1 @ X0))
% 0.44/0.64          | ~ (v1_relat_1 @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.64  thf('14', plain,
% 0.44/0.64      (![X15 : $i, X16 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.44/0.64  thf('15', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X0)
% 0.44/0.64          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.44/0.64             (k3_relat_1 @ X0)))),
% 0.44/0.64      inference('clc', [status(thm)], ['13', '14'])).
% 0.44/0.64  thf(t19_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.44/0.64       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.64  thf('16', plain,
% 0.44/0.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.64         (~ (r1_tarski @ X12 @ X13)
% 0.44/0.64          | ~ (r1_tarski @ X12 @ X14)
% 0.44/0.64          | (r1_tarski @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.44/0.64  thf('17', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X0)
% 0.44/0.64          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.44/0.64             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 0.44/0.64          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.44/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.64  thf('18', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X0)
% 0.44/0.64          | ~ (v1_relat_1 @ X1)
% 0.44/0.64          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.44/0.64             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 0.44/0.64          | ~ (v1_relat_1 @ X1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['10', '17'])).
% 0.44/0.64  thf('19', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.44/0.64           (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 0.44/0.64          | ~ (v1_relat_1 @ X1)
% 0.44/0.64          | ~ (v1_relat_1 @ X0))),
% 0.44/0.64      inference('simplify', [status(thm)], ['18'])).
% 0.44/0.64  thf(t34_relat_1, conjecture,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ A ) =>
% 0.44/0.65       ( ![B:$i]:
% 0.44/0.65         ( ( v1_relat_1 @ B ) =>
% 0.44/0.65           ( r1_tarski @
% 0.44/0.65             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.44/0.65             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i]:
% 0.44/0.65        ( ( v1_relat_1 @ A ) =>
% 0.44/0.65          ( ![B:$i]:
% 0.44/0.65            ( ( v1_relat_1 @ B ) =>
% 0.44/0.65              ( r1_tarski @
% 0.44/0.65                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.44/0.65                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.44/0.65          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('21', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.65  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('24', plain, ($false),
% 0.44/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.48/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
