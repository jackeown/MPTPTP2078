%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jkr2DeBpNg

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:07 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   50 (  69 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  314 ( 452 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X32 != X31 )
      | ( r2_hidden @ X32 @ X33 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X31: $i] :
      ( r2_hidden @ X31 @ ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ( X34 = X31 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34 = X31 )
      | ~ ( r2_hidden @ X34 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jkr2DeBpNg
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.33/0.53  % Solved by: fo/fo7.sh
% 0.33/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.53  % done 153 iterations in 0.101s
% 0.33/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.33/0.53  % SZS output start Refutation
% 0.33/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.33/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.53  thf(d1_tarski, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.33/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.33/0.53  thf('0', plain,
% 0.33/0.53      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.33/0.53         (((X32) != (X31))
% 0.33/0.53          | (r2_hidden @ X32 @ X33)
% 0.33/0.53          | ((X33) != (k1_tarski @ X31)))),
% 0.33/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.33/0.53  thf('1', plain, (![X31 : $i]: (r2_hidden @ X31 @ (k1_tarski @ X31))),
% 0.33/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.33/0.53  thf(t13_zfmisc_1, conjecture,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.33/0.53         ( k1_tarski @ A ) ) =>
% 0.33/0.53       ( ( A ) = ( B ) ) ))).
% 0.33/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.53    (~( ![A:$i,B:$i]:
% 0.33/0.53        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.33/0.53            ( k1_tarski @ A ) ) =>
% 0.33/0.53          ( ( A ) = ( B ) ) ) )),
% 0.33/0.53    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.33/0.53  thf('2', plain,
% 0.33/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.33/0.53         = (k1_tarski @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t98_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.33/0.53  thf('3', plain,
% 0.33/0.53      (![X17 : $i, X18 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ X17 @ X18)
% 0.33/0.53           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.33/0.53  thf(t92_xboole_1, axiom,
% 0.33/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.33/0.53  thf('4', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.33/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.33/0.53  thf(t91_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i,C:$i]:
% 0.33/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.33/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.33/0.53  thf('5', plain,
% 0.33/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.33/0.53           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.33/0.53  thf('6', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.33/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.33/0.53  thf(commutativity_k5_xboole_0, axiom,
% 0.33/0.53    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.33/0.53  thf('7', plain,
% 0.33/0.53      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.33/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.33/0.53  thf(t5_boole, axiom,
% 0.33/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.33/0.53  thf('8', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.33/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.33/0.53  thf('9', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.33/0.53  thf('10', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.33/0.53  thf('11', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.33/0.53           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['3', '10'])).
% 0.33/0.53  thf('12', plain,
% 0.33/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.33/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['2', '11'])).
% 0.33/0.53  thf('13', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.33/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.33/0.53  thf('14', plain,
% 0.33/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.33/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.33/0.53  thf(t100_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.33/0.53  thf('15', plain,
% 0.33/0.53      (![X10 : $i, X11 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X10 @ X11)
% 0.33/0.53           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.53  thf('16', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.33/0.53  thf('17', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k3_xboole_0 @ X1 @ X0)
% 0.33/0.53           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.33/0.53  thf('18', plain,
% 0.33/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.33/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['14', '17'])).
% 0.33/0.53  thf('19', plain,
% 0.33/0.53      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.33/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.33/0.53  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.33/0.53  thf('21', plain,
% 0.33/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.33/0.53         = (k1_tarski @ sk_B))),
% 0.33/0.53      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.33/0.53  thf(d4_xboole_0, axiom,
% 0.33/0.53    (![A:$i,B:$i,C:$i]:
% 0.33/0.53     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.33/0.53       ( ![D:$i]:
% 0.33/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.33/0.53           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.33/0.53  thf('22', plain,
% 0.33/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.33/0.53         (~ (r2_hidden @ X8 @ X7)
% 0.33/0.53          | (r2_hidden @ X8 @ X6)
% 0.33/0.53          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.33/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.33/0.53  thf('23', plain,
% 0.33/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.33/0.53         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.33/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.33/0.53  thf('24', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.33/0.53          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['21', '23'])).
% 0.33/0.53  thf('25', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['1', '24'])).
% 0.33/0.53  thf('26', plain,
% 0.33/0.53      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.33/0.53         (~ (r2_hidden @ X34 @ X33)
% 0.33/0.53          | ((X34) = (X31))
% 0.33/0.53          | ((X33) != (k1_tarski @ X31)))),
% 0.33/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.33/0.53  thf('27', plain,
% 0.33/0.53      (![X31 : $i, X34 : $i]:
% 0.33/0.53         (((X34) = (X31)) | ~ (r2_hidden @ X34 @ (k1_tarski @ X31)))),
% 0.33/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.33/0.53  thf('28', plain, (((sk_B) = (sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['25', '27'])).
% 0.33/0.53  thf('29', plain, (((sk_A) != (sk_B))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('30', plain, ($false),
% 0.33/0.53      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.33/0.53  
% 0.33/0.53  % SZS output end Refutation
% 0.33/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
