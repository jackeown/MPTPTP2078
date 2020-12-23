%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7vKpYPqGs

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  333 ( 430 expanded)
%              Number of equality atoms :   30 (  35 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t97_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
        & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
          & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t97_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_C )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','15'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ X3 @ X4 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('18',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) @ sk_C ),
    inference(simplify,[status(thm)],['22'])).

thf(t55_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ X3 @ X4 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7vKpYPqGs
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 50 iterations in 0.033s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(t97_xboole_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 0.20/0.49         ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 0.20/0.49       ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 0.20/0.49            ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 0.20/0.49          ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t97_xboole_1])).
% 0.20/0.49  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(t42_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.49       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X8) @ X7)
% 0.20/0.49           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X8 @ X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.49           sk_C) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C))
% 0.20/0.49            != (k1_xboole_0))
% 0.20/0.49          | (r1_tarski @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.49             sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | (r1_tarski @ 
% 0.20/0.49           (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.49            (k4_xboole_0 @ sk_B @ sk_A)) @ 
% 0.20/0.49           sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '10'])).
% 0.20/0.49  thf(t3_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('12', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.49  thf(t48_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.20/0.49           = (k3_xboole_0 @ X9 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf(l98_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k5_xboole_0 @ A @ B ) =
% 0.20/0.49       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((k5_xboole_0 @ X3 @ X4)
% 0.20/0.49           = (k4_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.49         = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.20/0.49            k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf(t5_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('19', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.49  thf('20', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | (r1_tarski @ 
% 0.20/0.49           (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.49            (k4_xboole_0 @ sk_B @ sk_A)) @ 
% 0.20/0.49           sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((r1_tarski @ 
% 0.20/0.49        (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.49         (k4_xboole_0 @ sk_B @ sk_A)) @ 
% 0.20/0.49        sk_C)),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf(t55_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.49       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ (k3_xboole_0 @ X11 @ X12))
% 0.20/0.49           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 0.20/0.49              (k4_xboole_0 @ X12 @ X11)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t55_xboole_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((k5_xboole_0 @ X3 @ X4)
% 0.20/0.49           = (k4_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         ((k5_xboole_0 @ X11 @ X12)
% 0.20/0.49           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 0.20/0.49              (k4_xboole_0 @ X12 @ X11)))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '26'])).
% 0.20/0.49  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
