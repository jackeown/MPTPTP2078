%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WlkgmMGRHa

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :  195 ( 224 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X42: $i] :
      ( ( ( k3_relat_1 @ X42 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('5',plain,
    ( ( ( k3_relat_1 @ o_0_0_xboole_0 )
      = ( k2_xboole_0 @ o_0_0_xboole_0 @ ( k2_relat_1 @ o_0_0_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ o_0_0_xboole_0 )
      = X6 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k3_relat_1 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['5','9','12'])).

thf(t63_relat_1,conjecture,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t63_relat_1])).

thf('14',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ( k3_relat_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['13','17'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('19',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ X32 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ o_0_0_xboole_0 )
      = X7 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['18','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WlkgmMGRHa
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 32 iterations in 0.021s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(t60_relat_1, axiom,
% 0.19/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.47  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.19/0.47  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.47  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.47  thf('3', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.19/0.47  thf(d6_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) =>
% 0.19/0.47       ( ( k3_relat_1 @ A ) =
% 0.19/0.47         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X42 : $i]:
% 0.19/0.47         (((k3_relat_1 @ X42)
% 0.19/0.47            = (k2_xboole_0 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42)))
% 0.19/0.47          | ~ (v1_relat_1 @ X42))),
% 0.19/0.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      ((((k3_relat_1 @ o_0_0_xboole_0)
% 0.19/0.47          = (k2_xboole_0 @ o_0_0_xboole_0 @ (k2_relat_1 @ o_0_0_xboole_0)))
% 0.19/0.47        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.47  thf('7', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.47  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.47  thf('9', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.47  thf(t1_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('10', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.47  thf('11', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.47  thf('12', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ o_0_0_xboole_0) = (X6))),
% 0.19/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      ((((k3_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.19/0.47        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['5', '9', '12'])).
% 0.19/0.47  thf(t63_relat_1, conjecture,
% 0.19/0.47    (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (( k3_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t63_relat_1])).
% 0.19/0.47  thf('14', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.47  thf('16', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.47  thf('17', plain, (((k3_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.19/0.47  thf('18', plain, (~ (v1_relat_1 @ o_0_0_xboole_0)),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['13', '17'])).
% 0.19/0.47  thf(d1_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) <=>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.47              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X32 : $i]: ((v1_relat_1 @ X32) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.19/0.47  thf(t3_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('20', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.47  thf('21', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.47  thf('22', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ o_0_0_xboole_0) = (X7))),
% 0.19/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf(d5_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.47       ( ![D:$i]:
% 0.19/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.47           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.47          | ~ (r2_hidden @ X4 @ X2)
% 0.19/0.47          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.47          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ o_0_0_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['22', '24'])).
% 0.19/0.47  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.19/0.47      inference('condensation', [status(thm)], ['25'])).
% 0.19/0.47  thf('27', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['19', '26'])).
% 0.19/0.47  thf('28', plain, ($false), inference('demod', [status(thm)], ['18', '27'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
