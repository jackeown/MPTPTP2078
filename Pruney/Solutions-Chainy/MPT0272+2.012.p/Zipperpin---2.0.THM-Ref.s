%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CDAqrXeai1

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  214 ( 240 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X42
        = ( k1_tarski @ X41 ) )
      | ( X42 = k1_xboole_0 )
      | ~ ( r1_tarski @ X42 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('10',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CDAqrXeai1
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 78 iterations in 0.019s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(t17_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.45      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.45  thf(l3_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X41 : $i, X42 : $i]:
% 0.20/0.45         (((X42) = (k1_tarski @ X41))
% 0.20/0.45          | ((X42) = (k1_xboole_0))
% 0.20/0.45          | ~ (r1_tarski @ X42 @ (k1_tarski @ X41)))),
% 0.20/0.45      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.20/0.45          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t100_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i]:
% 0.20/0.45         ((k4_xboole_0 @ X5 @ X6)
% 0.20/0.45           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.20/0.45            = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.20/0.45          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf(t92_xboole_1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.45  thf('5', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.20/0.45          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.20/0.45      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.45  thf(d7_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.45       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X2 : $i, X4 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.45          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 0.20/0.45          | (r1_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.20/0.45          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.45  thf(t69_zfmisc_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.20/0.45       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.20/0.45          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.45        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('12', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.45      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.45  thf(t83_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i]:
% 0.20/0.45         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.20/0.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('16', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
