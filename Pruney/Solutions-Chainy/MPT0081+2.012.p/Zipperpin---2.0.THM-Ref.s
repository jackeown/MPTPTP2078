%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NlyLHsHznM

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  203 ( 274 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t74_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t74_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X8 ) @ X9 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X8 ) @ X9 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NlyLHsHznM
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:21:36 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 25 iterations in 0.017s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.43  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(t74_xboole_1, conjecture,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.43          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.43        ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.43             ( r1_xboole_0 @ A @ B ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t74_xboole_1])).
% 0.20/0.43  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(t48_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (![X12 : $i, X13 : $i]:
% 0.20/0.43         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.43           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.43      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.43  thf('2', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(d7_xboole_0, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.43       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.43      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.43  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.43  thf(t49_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.20/0.43       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.43         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.43           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.43      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.20/0.43           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.43      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.43  thf(t41_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.43       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.43  thf('7', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.43         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.43           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.43  thf(t46_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (![X8 : $i, X9 : $i]:
% 0.20/0.43         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.43         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.43           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.43  thf('10', plain,
% 0.20/0.43      (![X8 : $i, X9 : $i]:
% 0.20/0.43         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X8) @ X9) = (k1_xboole_0))),
% 0.20/0.43      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ X1) @ X0)
% 0.20/0.43           = (k1_xboole_0))),
% 0.20/0.43      inference('sup+', [status(thm)], ['7', '10'])).
% 0.20/0.43  thf('12', plain,
% 0.20/0.43      (![X8 : $i, X9 : $i]:
% 0.20/0.43         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X8) @ X9) = (k1_xboole_0))),
% 0.20/0.43      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.43  thf('13', plain,
% 0.20/0.43      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.43      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.20/0.43      inference('demod', [status(thm)], ['6', '13'])).
% 0.20/0.43  thf('15', plain,
% 0.20/0.43      (![X0 : $i, X2 : $i]:
% 0.20/0.43         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.43      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.43  thf('16', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.43          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.43  thf('17', plain,
% 0.20/0.43      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.43  thf('18', plain,
% 0.20/0.43      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))),
% 0.20/0.43      inference('sup+', [status(thm)], ['1', '17'])).
% 0.20/0.43  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
