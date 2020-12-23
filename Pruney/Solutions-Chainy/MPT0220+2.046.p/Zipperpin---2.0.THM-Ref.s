%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CCSML4pBDB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  66 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  622 ( 737 expanded)
%              Number of equality atoms :   44 (  53 expanded)
%              Maximal formula depth    :   20 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k5_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t133_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k7_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t133_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X7 @ X7 @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k5_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k7_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t133_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X7 @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k6_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 )
      = ( k6_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k5_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k4_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('15',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k6_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      = ( k5_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k7_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_enumset1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k4_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','29'])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('32',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','30','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CCSML4pBDB
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 83 iterations in 0.044s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.49                                           $i > $i > $i).
% 0.21/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.49                                           $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(t14_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.49       ( k2_tarski @ A @ B ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.49          ( k2_tarski @ A @ B ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.49         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t70_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf(t74_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.49     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.49       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.49         ((k5_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.21/0.49           = (k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.21/0.49      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf(t133_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.49     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.21/0.49       ( k2_xboole_0 @
% 0.21/0.49         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 0.21/0.49         X13 : $i, X14 : $i]:
% 0.21/0.49         ((k7_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.49           = (k2_xboole_0 @ 
% 0.21/0.49              (k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12) @ 
% 0.21/0.49              (k2_tarski @ X13 @ X14)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t133_enumset1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.21/0.49         X7 : $i, X8 : $i]:
% 0.21/0.49         ((k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.49           = (k2_xboole_0 @ (k5_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.49              (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((k7_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6)
% 0.21/0.49           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.21/0.49              (k1_enumset1 @ X7 @ X7 @ X6)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.49         ((k5_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.21/0.49           = (k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.21/0.49      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 0.21/0.49         X13 : $i, X14 : $i]:
% 0.21/0.49         ((k7_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.49           = (k2_xboole_0 @ 
% 0.21/0.49              (k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12) @ 
% 0.21/0.49              (k2_tarski @ X13 @ X14)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t133_enumset1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((k7_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6)
% 0.21/0.49           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.21/0.49              (k2_tarski @ X7 @ X6)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf(t67_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.49     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.49       ( k2_xboole_0 @
% 0.21/0.49         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, 
% 0.21/0.49         X22 : $i]:
% 0.21/0.49         ((k6_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.21/0.49           = (k2_xboole_0 @ 
% 0.21/0.49              (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20) @ 
% 0.21/0.49              (k2_tarski @ X21 @ X22)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((k7_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6)
% 0.21/0.49           = (k6_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.49         ((k5_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.21/0.49           = (k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.21/0.49      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.49  thf(t73_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.49       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.49         ((k4_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.21/0.49           = (k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.21/0.49      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.49           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf(t75_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.49     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.49       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.21/0.49         ((k6_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.21/0.49           = (k5_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 0.21/0.49      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.49           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf(t72_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32)
% 0.21/0.49           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 0.21/0.49      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.49           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k7_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.49           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['11', '18'])).
% 0.21/0.49  thf(t71_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 0.21/0.49           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k7_enumset1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 0.21/0.49           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ (k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2) @ 
% 0.21/0.49           (k1_enumset1 @ X1 @ X1 @ X0)) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.49         ((k4_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.21/0.49           = (k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.21/0.49      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32)
% 0.21/0.49           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 0.21/0.49      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 0.21/0.49           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.21/0.49           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23', '24', '25', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.49           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf('32', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '30', '31'])).
% 0.21/0.49  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
