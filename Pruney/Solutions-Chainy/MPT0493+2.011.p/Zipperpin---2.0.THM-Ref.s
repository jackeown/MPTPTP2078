%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fI32fcKC1A

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:03 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  299 ( 429 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t91_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_relat_1])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('15',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('21',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fI32fcKC1A
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 196 iterations in 0.107s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.60  thf(d5_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.39/0.60       ( ![D:$i]:
% 0.39/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.39/0.60         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.39/0.60          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 0.39/0.60          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.39/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.60  thf(t3_boole, axiom,
% 0.39/0.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.60  thf('1', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X10 @ X9)
% 0.39/0.60          | ~ (r2_hidden @ X10 @ X8)
% 0.39/0.60          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X10 @ X8)
% 0.39/0.60          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['1', '3'])).
% 0.39/0.60  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.60      inference('condensation', [status(thm)], ['4'])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.60          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['0', '5'])).
% 0.39/0.60  thf(t91_relat_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.60         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i]:
% 0.39/0.60        ( ( v1_relat_1 @ B ) =>
% 0.39/0.60          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.60            ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t91_relat_1])).
% 0.39/0.60  thf('7', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(d3_tarski, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X2 @ X3)
% 0.39/0.60          | (r2_hidden @ X2 @ X4)
% 0.39/0.60          | ~ (r1_tarski @ X3 @ X4))),
% 0.39/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0))
% 0.39/0.60          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['6', '9'])).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.39/0.60         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.39/0.60          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 0.39/0.60          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.39/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      ((((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.39/0.60        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 0.39/0.60           k1_xboole_0)
% 0.39/0.60        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      (((r2_hidden @ (sk_D @ k1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 0.39/0.60         k1_xboole_0)
% 0.39/0.60        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.39/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.60  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.60      inference('condensation', [status(thm)], ['4'])).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.60      inference('clc', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf(t48_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      (![X15 : $i, X16 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.39/0.60           = (k3_xboole_0 @ X15 @ X16))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.39/0.60         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.39/0.60  thf('18', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.60  thf('19', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.60  thf(t90_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.39/0.60         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      (![X22 : $i, X23 : $i]:
% 0.39/0.60         (((k1_relat_1 @ (k7_relat_1 @ X22 @ X23))
% 0.39/0.60            = (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23))
% 0.39/0.60          | ~ (v1_relat_1 @ X22))),
% 0.39/0.60      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.39/0.60  thf('21', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) != (sk_A))
% 0.39/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.60  thf('23', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.60  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('25', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) != (sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.39/0.60  thf('26', plain, ($false),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['19', '25'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
