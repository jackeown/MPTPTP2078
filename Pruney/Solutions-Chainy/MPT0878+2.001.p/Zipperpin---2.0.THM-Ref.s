%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yumAxEejRs

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 131 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  362 (1318 expanded)
%              Number of equality atoms :   75 ( 264 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t38_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_zfmisc_1 @ A @ A @ A )
        = ( k3_zfmisc_1 @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_zfmisc_1 @ A @ A @ A )
          = ( k3_zfmisc_1 @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t38_mcart_1])).

thf('0',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t115_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ A )
        = ( k2_zfmisc_1 @ B @ B ) )
     => ( A = B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( ( k2_zfmisc_1 @ X4 @ X4 )
       != ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t115_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X6 @ X5 )
       != ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3 = X0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['16'])).

thf('18',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['19','20'])).

thf('23',plain,
    ( ( sk_B = sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != sk_A ) ),
    inference(demod,[status(thm)],['9','21','22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
 != sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['19','20'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['19','20'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['25','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yumAxEejRs
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 50 iterations in 0.021s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(t38_mcart_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.21/0.48       ( ( A ) = ( B ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.21/0.48          ( ( A ) = ( B ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t38_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf(t113_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.48          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.48  thf(t115_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_zfmisc_1 @ A @ A ) = ( k2_zfmisc_1 @ B @ B ) ) =>
% 0.21/0.48       ( ( A ) = ( B ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         (((X4) = (X3)) | ((k2_zfmisc_1 @ X4 @ X4) != (k2_zfmisc_1 @ X3 @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t115_zfmisc_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_xboole_0) != (k2_zfmisc_1 @ X0 @ X0)) | ((k1_xboole_0) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.21/0.48      inference('clc', [status(thm)], ['4', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf(t134_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (((X5) = (k1_xboole_0))
% 0.21/0.48          | ((X6) = (k1_xboole_0))
% 0.21/0.48          | ((k2_zfmisc_1 @ X6 @ X5) != (k2_zfmisc_1 @ X7 @ X8))
% 0.21/0.48          | ((X5) = (X8)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X4 @ X3) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X3) = (X0))
% 0.21/0.48          | ((X4) = (k1_xboole_0))
% 0.21/0.48          | ((X3) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X1 @ X0) != (k3_zfmisc_1 @ sk_A @ sk_A @ sk_A))
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ sk_A @ sk_A @ sk_A))
% 0.21/0.48          | ((X0) = (sk_B))
% 0.21/0.48          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0))
% 0.21/0.48        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (sk_B)))),
% 0.21/0.48      inference('eq_res', [status(thm)], ['16'])).
% 0.21/0.48  thf('18', plain, (((sk_A) != (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0))
% 0.21/0.48        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_xboole_0) != (k2_zfmisc_1 @ X0 @ X0)) | ((k1_xboole_0) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('21', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((((sk_B) = (sk_A)) | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '21', '22'])).
% 0.21/0.48  thf('24', plain, (((sk_A) != (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (sk_A))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.21/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ X1 @ X0 @ sk_A) = (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.48  thf('32', plain, (((sk_A) != (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '31'])).
% 0.21/0.48  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
