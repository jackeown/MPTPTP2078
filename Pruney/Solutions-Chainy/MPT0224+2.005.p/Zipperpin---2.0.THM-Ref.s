%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s98u2e9xgF

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  61 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  320 ( 397 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t19_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t19_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k1_tarski @ X26 ) @ ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['6','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s98u2e9xgF
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 212 iterations in 0.111s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(t19_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.57       ( k1_tarski @ A ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.57          ( k1_tarski @ A ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t19_zfmisc_1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.57         != (k1_tarski @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t12_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X26 : $i, X27 : $i]:
% 0.21/0.57         (r1_tarski @ (k1_tarski @ X26) @ (k2_tarski @ X26 @ X27))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.57  thf(l32_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X13 : $i, X15 : $i]:
% 0.21/0.57         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.21/0.57          | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.21/0.57           = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(t48_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.21/0.57           = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)
% 0.21/0.57           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.57  thf(d10_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('8', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.21/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X13 : $i, X15 : $i]:
% 0.21/0.57         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.21/0.57          | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.21/0.57           = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf(t47_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 0.21/0.57           = (k4_xboole_0 @ X16 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i]:
% 0.21/0.57         ((r1_tarski @ X13 @ X14)
% 0.21/0.57          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.57  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['12', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X10 : $i, X12 : $i]:
% 0.21/0.57         (((X10) = (X12))
% 0.21/0.57          | ~ (r1_tarski @ X12 @ X10)
% 0.21/0.57          | ~ (r1_tarski @ X10 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.57          | ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X1 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf(d5_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.57       ( ![D:$i]:
% 0.21/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.57          | (r2_hidden @ X8 @ X5)
% 0.21/0.57          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.57         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.57          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X1 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.21/0.57          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.57  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['21', '28'])).
% 0.21/0.57  thf('30', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '29'])).
% 0.21/0.57  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
