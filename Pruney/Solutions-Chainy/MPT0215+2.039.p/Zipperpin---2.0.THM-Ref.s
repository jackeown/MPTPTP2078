%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Sv9oHliGH6

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  55 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  383 ( 419 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t8_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t8_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k6_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k5_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X6 @ X6 @ X5 @ X4 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k5_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','20'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('22',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 = X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('23',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Sv9oHliGH6
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 69 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.49                                           $i > $i).
% 0.21/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(t8_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t8_zfmisc_1])).
% 0.21/0.49  thf('0', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t70_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf(t72_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23)
% 0.21/0.49           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 0.21/0.49      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.49  thf(t71_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 0.21/0.49           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('6', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t75_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.49     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.49       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.49         ((k6_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41)
% 0.21/0.49           = (k5_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41))),
% 0.21/0.49      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.21/0.49  thf(l75_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.49     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.49       ( k2_xboole_0 @
% 0.21/0.49         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 0.21/0.49         X13 : $i]:
% 0.21/0.49         ((k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.21/0.49              (k2_enumset1 @ X10 @ X11 @ X12 @ X13)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.21/0.49  thf(t7_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (r1_tarski @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.21/0.49          (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (r1_tarski @ (k2_enumset1 @ X6 @ X6 @ X5 @ X4) @ 
% 0.21/0.49          (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['8', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 0.21/0.49           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.21/0.49          (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_tarski @ X0) @ 
% 0.21/0.49          (k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['7', '14'])).
% 0.21/0.49  thf(t74_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.49     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.49       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.49         ((k5_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.21/0.49           = (k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 0.21/0.49      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.49  thf(t73_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.49       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.49         ((k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.21/0.49           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.21/0.49      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_tarski @ X0) @ (k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['4', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '19'])).
% 0.21/0.49  thf('21', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '20'])).
% 0.21/0.49  thf(t6_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.49       ( ( A ) = ( B ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X42 : $i, X43 : $i]:
% 0.21/0.49         (((X43) = (X42))
% 0.21/0.49          | ~ (r1_tarski @ (k1_tarski @ X43) @ (k1_tarski @ X42)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.49  thf('23', plain, (((sk_B) = (sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
