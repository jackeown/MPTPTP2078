%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ghsXUZgWwa

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:57 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   47 (  59 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  213 ( 294 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ X14 @ ( k3_xboole_0 @ ( k2_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = ( k10_relat_1 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_relat_1 @ X16 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('9',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('17',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','17'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6','19','20'])).

thf('22',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ghsXUZgWwa
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 19:59:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 22 iterations in 0.015s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(t172_relat_1, conjecture,
% 0.23/0.49    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.23/0.49  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t60_relat_1, axiom,
% 0.23/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.23/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.49  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.49  thf(t168_relat_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( v1_relat_1 @ B ) =>
% 0.23/0.49       ( ( k10_relat_1 @ B @ A ) =
% 0.23/0.49         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X14 : $i, X15 : $i]:
% 0.23/0.49         (((k10_relat_1 @ X14 @ X15)
% 0.23/0.49            = (k10_relat_1 @ X14 @ (k3_xboole_0 @ (k2_relat_1 @ X14) @ X15)))
% 0.23/0.49          | ~ (v1_relat_1 @ X14))),
% 0.23/0.49      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         (((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.23/0.49            = (k10_relat_1 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 0.23/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.49  thf('4', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.23/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.49  thf(t28_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i]:
% 0.23/0.49         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.49  thf(t169_relat_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( v1_relat_1 @ A ) =>
% 0.23/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X16 : $i]:
% 0.23/0.49         (((k10_relat_1 @ X16 @ (k2_relat_1 @ X16)) = (k1_relat_1 @ X16))
% 0.23/0.49          | ~ (v1_relat_1 @ X16))),
% 0.23/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.23/0.49        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.23/0.49  thf('10', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.23/0.49        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.49  thf(d1_relat_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( v1_relat_1 @ A ) <=>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ~( ( r2_hidden @ B @ A ) & 
% 0.23/0.49              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X11 : $i]: ((v1_relat_1 @ X11) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.23/0.49      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.23/0.49  thf(t2_boole, axiom,
% 0.23/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.23/0.49  thf(t4_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.23/0.49          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.49  thf('16', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.23/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.49  thf('17', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.23/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.49  thf('18', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.49      inference('sup-', [status(thm)], ['12', '17'])).
% 0.23/0.49  thf('19', plain,
% 0.23/0.49      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.49      inference('demod', [status(thm)], ['11', '18'])).
% 0.23/0.49  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.49      inference('sup-', [status(thm)], ['12', '17'])).
% 0.23/0.49  thf('21', plain,
% 0.23/0.49      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.23/0.49      inference('demod', [status(thm)], ['3', '6', '19', '20'])).
% 0.23/0.49  thf('22', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.49      inference('demod', [status(thm)], ['0', '21'])).
% 0.23/0.49  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
