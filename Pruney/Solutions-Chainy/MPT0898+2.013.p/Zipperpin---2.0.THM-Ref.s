%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OuCoQdau69

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 118 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  447 (1364 expanded)
%              Number of equality atoms :   75 ( 179 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','21'])).

thf('23',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OuCoQdau69
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:30:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 63 iterations in 0.041s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(t58_mcart_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.20/0.49       ( ( A ) = ( B ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.20/0.49          ( ( A ) = ( B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.49         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t55_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.49       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.49         (((k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 0.20/0.49          | ((X23) = (k1_xboole_0))
% 0.20/0.49          | ((X22) = (k1_xboole_0))
% 0.20/0.49          | ((X21) = (k1_xboole_0))
% 0.20/0.49          | ((X20) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf(d3_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.49           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(t53_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.20/0.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.49         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18) @ 
% 0.20/0.49              X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.49         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.49           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.49           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.49         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.49           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.49  thf(t37_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.49     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.49       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         (((k3_zfmisc_1 @ X10 @ X11 @ X12) = (k1_xboole_0))
% 0.20/0.49          | ((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.20/0.49          | ((X12) = (X15)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X4) = (X0))
% 0.20/0.49          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.20/0.49            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.20/0.49          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.49          | ((X0) = (sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.49            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.20/0.49          | ((X0) = (sk_B))
% 0.20/0.49          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.49           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.49            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.20/0.49          | ((X0) = (sk_B))
% 0.20/0.49          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (sk_B)))),
% 0.20/0.49      inference('eq_res', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain, (((sk_A) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '21'])).
% 0.20/0.49  thf('23', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.49         (((k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 0.20/0.49          | ((X23) = (k1_xboole_0))
% 0.20/0.49          | ((X22) = (k1_xboole_0))
% 0.20/0.49          | ((X21) = (k1_xboole_0))
% 0.20/0.49          | ((X20) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.49  thf('28', plain, (((sk_A) = (sk_B))),
% 0.20/0.49      inference('sup+', [status(thm)], ['23', '27'])).
% 0.20/0.49  thf('29', plain, (((sk_A) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
