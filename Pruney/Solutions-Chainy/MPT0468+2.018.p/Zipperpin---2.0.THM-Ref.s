%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DcX7xMaM4h

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  40 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 240 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r1_tarski @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t56_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ! [B: $i,C: $i] :
              ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_relat_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_A @ X1 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_xboole_0 @ X0 @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DcX7xMaM4h
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 10 iterations in 0.011s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.46  thf('0', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.46  thf(d3_relat_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ A ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.46           ( ![C:$i,D:$i]:
% 0.22/0.46             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.22/0.46               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i]:
% 0.22/0.46         ((r2_hidden @ (k4_tarski @ (sk_C @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X5)
% 0.22/0.46          | (r1_tarski @ X5 @ X4)
% 0.22/0.46          | ~ (v1_relat_1 @ X5))),
% 0.22/0.46      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.46  thf(t56_relat_1, conjecture,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ A ) =>
% 0.22/0.46       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.22/0.46         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i]:
% 0.22/0.46        ( ( v1_relat_1 @ A ) =>
% 0.22/0.46          ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.22/0.46            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t56_relat_1])).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X9 : $i, X10 : $i]: ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X0 : $i]: (~ (v1_relat_1 @ sk_A) | (r1_tarski @ sk_A @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.46  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('5', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.22/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.46  thf(t67_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.22/0.46         ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.46       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         (((X1) = (k1_xboole_0))
% 0.22/0.46          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.46          | ~ (r1_tarski @ X1 @ X3)
% 0.22/0.46          | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.46          | ~ (r1_tarski @ sk_A @ X1)
% 0.22/0.46          | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.46  thf('8', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.22/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_xboole_0 @ X0 @ X1) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.46  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('11', plain, (![X0 : $i, X1 : $i]: ~ (r1_xboole_0 @ X0 @ X1)),
% 0.22/0.46      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf('12', plain, ($false), inference('sup-', [status(thm)], ['0', '11'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
