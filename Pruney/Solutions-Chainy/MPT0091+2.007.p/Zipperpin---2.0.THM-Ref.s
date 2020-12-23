%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lkshWcfM9r

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:43 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   47 (  59 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  274 ( 376 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t84_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C )
          & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','26'])).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k4_xboole_0 @ X7 @ X9 )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,
    ( ( sk_A != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lkshWcfM9r
% 0.09/0.32  % Computer   : n021.cluster.edu
% 0.09/0.32  % Model      : x86_64 x86_64
% 0.09/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.32  % Memory     : 8042.1875MB
% 0.09/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.32  % CPULimit   : 60
% 0.09/0.32  % DateTime   : Tue Dec  1 10:55:49 EST 2020
% 0.09/0.33  % CPUTime    : 
% 0.09/0.33  % Running portfolio for 600 s
% 0.09/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.09/0.33  % Number of cores: 8
% 0.09/0.33  % Python version: Python 3.6.8
% 0.09/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 48 iterations in 0.026s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(t84_xboole_1, conjecture,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.18/0.46          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.46        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.18/0.46             ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t84_xboole_1])).
% 0.18/0.46  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t83_xboole_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      (![X7 : $i, X8 : $i]:
% 0.18/0.46         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.18/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.18/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.46  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('5', plain,
% 0.18/0.46      (![X7 : $i, X8 : $i]:
% 0.18/0.46         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.18/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.18/0.46  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.18/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.18/0.46  thf(t48_xboole_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      (![X2 : $i, X3 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.18/0.46           = (k3_xboole_0 @ X2 @ X3))),
% 0.18/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.18/0.46  thf(t3_boole, axiom,
% 0.18/0.46    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.46  thf('9', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      (![X2 : $i, X3 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.18/0.46           = (k3_xboole_0 @ X2 @ X3))),
% 0.18/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.18/0.46  thf('11', plain,
% 0.18/0.46      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.18/0.46      inference('sup+', [status(thm)], ['9', '10'])).
% 0.18/0.46  thf(t2_boole, axiom,
% 0.18/0.46    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.18/0.46  thf('12', plain,
% 0.18/0.46      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.46      inference('cnf', [status(esa)], [t2_boole])).
% 0.18/0.46  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.18/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.18/0.46  thf('14', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.18/0.46      inference('demod', [status(thm)], ['8', '13'])).
% 0.18/0.46  thf(t52_xboole_1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.18/0.46       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.18/0.46  thf('15', plain,
% 0.18/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.18/0.46           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X6)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.18/0.46  thf('16', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.18/0.46           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.18/0.46      inference('sup+', [status(thm)], ['14', '15'])).
% 0.18/0.46  thf('17', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.46  thf('18', plain,
% 0.18/0.46      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.46      inference('cnf', [status(esa)], [t2_boole])).
% 0.18/0.46  thf('19', plain,
% 0.18/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.18/0.46           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X6)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.18/0.46  thf('20', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0))
% 0.18/0.46           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.18/0.46      inference('sup+', [status(thm)], ['18', '19'])).
% 0.18/0.46  thf('21', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.46  thf('22', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ X0 @ X1)
% 0.18/0.46           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.18/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.18/0.46  thf('23', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.18/0.46      inference('sup+', [status(thm)], ['17', '22'])).
% 0.18/0.46  thf('24', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.46  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.18/0.46      inference('sup+', [status(thm)], ['23', '24'])).
% 0.18/0.46  thf('26', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.18/0.46           = (k4_xboole_0 @ sk_A @ X0))),
% 0.18/0.46      inference('demod', [status(thm)], ['16', '25'])).
% 0.18/0.46  thf('27', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.18/0.46      inference('demod', [status(thm)], ['3', '26'])).
% 0.18/0.46  thf('28', plain,
% 0.18/0.46      (![X7 : $i, X9 : $i]:
% 0.18/0.46         ((r1_xboole_0 @ X7 @ X9) | ((k4_xboole_0 @ X7 @ X9) != (X7)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.18/0.46  thf('29', plain, ((((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.18/0.46  thf('30', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.46      inference('simplify', [status(thm)], ['29'])).
% 0.18/0.46  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
