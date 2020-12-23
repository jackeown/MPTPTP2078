%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QkWhpDHFe3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:32 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   49 (  90 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  231 ( 481 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t62_xboole_1,conjecture,(
    ! [A: $i] :
      ~ ( r2_xboole_0 @ A @ k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( r2_xboole_0 @ A @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t62_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t59_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r2_xboole_0 @ X15 @ X16 )
      | ( r2_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','22'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('25',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('27',plain,(
    ~ ( r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','22'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QkWhpDHFe3
% 0.16/0.37  % Computer   : n016.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:50:04 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.46  % Solved by: fo/fo7.sh
% 0.23/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.46  % done 60 iterations in 0.015s
% 0.23/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.46  % SZS output start Refutation
% 0.23/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.46  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.23/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.46  thf(t62_xboole_1, conjecture,
% 0.23/0.46    (![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ))).
% 0.23/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.46    (~( ![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ) )),
% 0.23/0.46    inference('cnf.neg', [status(esa)], [t62_xboole_1])).
% 0.23/0.46  thf('0', plain, ((r2_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf(t1_boole, axiom,
% 0.23/0.46    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.46  thf('1', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.23/0.46      inference('cnf', [status(esa)], [t1_boole])).
% 0.23/0.46  thf(t29_xboole_1, axiom,
% 0.23/0.46    (![A:$i,B:$i,C:$i]:
% 0.23/0.46     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.23/0.46  thf('2', plain,
% 0.23/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.46         (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X10))),
% 0.23/0.46      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.23/0.46  thf('3', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.23/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.46  thf(t3_xboole_1, axiom,
% 0.23/0.46    (![A:$i]:
% 0.23/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.46  thf('4', plain,
% 0.23/0.46      (![X11 : $i]:
% 0.23/0.46         (((X11) = (k1_xboole_0)) | ~ (r1_tarski @ X11 @ k1_xboole_0))),
% 0.23/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.23/0.46  thf('5', plain,
% 0.23/0.46      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.46  thf(t47_xboole_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.46  thf('6', plain,
% 0.23/0.46      (![X12 : $i, X13 : $i]:
% 0.23/0.46         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.23/0.46           = (k4_xboole_0 @ X12 @ X13))),
% 0.23/0.46      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.23/0.46  thf('7', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.23/0.46           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.23/0.46      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.46  thf('8', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.23/0.46      inference('cnf', [status(esa)], [t1_boole])).
% 0.23/0.46  thf('9', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.23/0.46      inference('cnf', [status(esa)], [t1_boole])).
% 0.23/0.46  thf(t21_xboole_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.23/0.46  thf('10', plain,
% 0.23/0.46      (![X6 : $i, X7 : $i]:
% 0.23/0.46         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.23/0.46      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.23/0.46  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.46      inference('sup+', [status(thm)], ['9', '10'])).
% 0.23/0.46  thf('12', plain,
% 0.23/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.46         (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X10))),
% 0.23/0.46      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.23/0.46  thf('13', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.23/0.46  thf('14', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.23/0.46      inference('sup+', [status(thm)], ['8', '13'])).
% 0.23/0.46  thf(l32_xboole_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.46  thf('15', plain,
% 0.23/0.46      (![X2 : $i, X4 : $i]:
% 0.23/0.46         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.23/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.46  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.46  thf('17', plain,
% 0.23/0.46      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.23/0.46      inference('demod', [status(thm)], ['7', '16'])).
% 0.23/0.46  thf('18', plain,
% 0.23/0.46      (![X2 : $i, X3 : $i]:
% 0.23/0.46         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.23/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.46  thf('19', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.46  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.23/0.46      inference('simplify', [status(thm)], ['19'])).
% 0.23/0.46  thf(t59_xboole_1, axiom,
% 0.23/0.46    (![A:$i,B:$i,C:$i]:
% 0.23/0.46     ( ( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.23/0.46       ( r2_xboole_0 @ A @ C ) ))).
% 0.23/0.46  thf('21', plain,
% 0.23/0.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.46         (~ (r1_tarski @ X14 @ X15)
% 0.23/0.46          | ~ (r2_xboole_0 @ X15 @ X16)
% 0.23/0.46          | (r2_xboole_0 @ X14 @ X16))),
% 0.23/0.46      inference('cnf', [status(esa)], [t59_xboole_1])).
% 0.23/0.46  thf('22', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((r2_xboole_0 @ k1_xboole_0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.23/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.46  thf('23', plain, ((r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.23/0.46      inference('sup-', [status(thm)], ['0', '22'])).
% 0.23/0.46  thf(t6_xboole_0, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.23/0.46          ( ![C:$i]:
% 0.23/0.46            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.23/0.46  thf('24', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (~ (r2_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.23/0.46      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.23/0.46  thf('25', plain,
% 0.23/0.46      ((r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.23/0.46      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.46  thf('26', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (~ (r2_xboole_0 @ X0 @ X1) | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.23/0.46      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.23/0.46  thf('27', plain, (~ (r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.23/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.46  thf('28', plain, ((r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.23/0.46      inference('sup-', [status(thm)], ['0', '22'])).
% 0.23/0.46  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.46  
% 0.23/0.46  % SZS output end Refutation
% 0.23/0.46  
% 0.23/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
