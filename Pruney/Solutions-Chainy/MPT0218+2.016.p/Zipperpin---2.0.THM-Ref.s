%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ClrvdkcYjh

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:02 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   67 (  73 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  567 ( 636 expanded)
%              Number of equality atoms :   42 (  48 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t12_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('5',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('17',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','19'])).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ClrvdkcYjh
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:20:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.60/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.81  % Solved by: fo/fo7.sh
% 0.60/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.81  % done 343 iterations in 0.366s
% 0.60/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.81  % SZS output start Refutation
% 0.60/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.81  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.60/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.81  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.60/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.81  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.60/0.81  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.60/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.81  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.60/0.81  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.60/0.81                                           $i > $i).
% 0.60/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.81  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.60/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.81  thf(t12_zfmisc_1, conjecture,
% 0.60/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.60/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.81    (~( ![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )),
% 0.60/0.81    inference('cnf.neg', [status(esa)], [t12_zfmisc_1])).
% 0.60/0.81  thf('0', plain,
% 0.60/0.81      (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(t70_enumset1, axiom,
% 0.60/0.81    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.60/0.81  thf('1', plain,
% 0.60/0.81      (![X23 : $i, X24 : $i]:
% 0.60/0.81         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.60/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.81  thf('2', plain,
% 0.60/0.81      (![X23 : $i, X24 : $i]:
% 0.60/0.81         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.60/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.81  thf(t69_enumset1, axiom,
% 0.60/0.81    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.81  thf('3', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.60/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.81  thf('4', plain,
% 0.60/0.81      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['2', '3'])).
% 0.60/0.81  thf(t75_enumset1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.60/0.81     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.60/0.81       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.60/0.81  thf('5', plain,
% 0.60/0.81      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.60/0.81         ((k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.60/0.81           = (k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.60/0.81      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.60/0.81  thf(t74_enumset1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.60/0.81     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.60/0.81       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.60/0.81  thf('6', plain,
% 0.60/0.81      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.60/0.81         ((k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.60/0.81           = (k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.60/0.81      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.60/0.81  thf('7', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.81         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.81           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['5', '6'])).
% 0.60/0.81  thf(t73_enumset1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.60/0.81     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.60/0.81       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.60/0.81  thf('8', plain,
% 0.60/0.81      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.60/0.81         ((k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.60/0.81           = (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.60/0.81      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.60/0.81  thf('9', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.81         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.81           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['7', '8'])).
% 0.60/0.81  thf(t72_enumset1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.81     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.60/0.81  thf('10', plain,
% 0.60/0.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.60/0.81         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 0.60/0.81           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 0.60/0.81      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.60/0.81  thf('11', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.81         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.81           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['9', '10'])).
% 0.60/0.81  thf('12', plain,
% 0.60/0.81      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.60/0.81         ((k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.60/0.81           = (k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.60/0.81      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.60/0.81  thf(t68_enumset1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.60/0.81     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.60/0.81       ( k2_xboole_0 @
% 0.60/0.81         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.60/0.81  thf('13', plain,
% 0.60/0.81      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.60/0.81         X21 : $i]:
% 0.60/0.81         ((k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.60/0.81           = (k2_xboole_0 @ 
% 0.60/0.81              (k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20) @ 
% 0.60/0.81              (k1_tarski @ X21)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.60/0.81  thf('14', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.81         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.60/0.81           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.60/0.81              (k1_tarski @ X6)))),
% 0.60/0.81      inference('sup+', [status(thm)], ['12', '13'])).
% 0.60/0.81  thf('15', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.81         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.81           = (k2_xboole_0 @ (k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1) @ 
% 0.60/0.81              (k1_tarski @ X0)))),
% 0.60/0.81      inference('sup+', [status(thm)], ['11', '14'])).
% 0.60/0.81  thf('16', plain,
% 0.60/0.81      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.60/0.81         ((k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.60/0.81           = (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.60/0.81      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.60/0.81  thf('17', plain,
% 0.60/0.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.60/0.81         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 0.60/0.81           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 0.60/0.81      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.60/0.81  thf(t71_enumset1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.60/0.81  thf('18', plain,
% 0.60/0.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.81         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 0.60/0.81           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.60/0.81      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.60/0.81  thf('19', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.81         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.81           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.60/0.81  thf('20', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.60/0.81           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.60/0.81      inference('sup+', [status(thm)], ['4', '19'])).
% 0.60/0.81  thf('21', plain,
% 0.60/0.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.81         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 0.60/0.81           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.60/0.81      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.60/0.81  thf('22', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.60/0.81           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.60/0.81      inference('demod', [status(thm)], ['20', '21'])).
% 0.60/0.81  thf(t98_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.60/0.81  thf('23', plain,
% 0.60/0.81      (![X12 : $i, X13 : $i]:
% 0.60/0.81         ((k2_xboole_0 @ X12 @ X13)
% 0.60/0.81           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.60/0.81  thf(t96_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.60/0.81  thf('24', plain,
% 0.60/0.81      (![X10 : $i, X11 : $i]:
% 0.60/0.81         (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ (k5_xboole_0 @ X10 @ X11))),
% 0.60/0.81      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.60/0.81  thf('25', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (r1_tarski @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 0.60/0.81          (k2_xboole_0 @ X1 @ X0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['23', '24'])).
% 0.60/0.81  thf('26', plain,
% 0.60/0.81      (![X12 : $i, X13 : $i]:
% 0.60/0.81         ((k2_xboole_0 @ X12 @ X13)
% 0.60/0.81           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.60/0.81  thf(t49_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.60/0.81       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.60/0.81  thf('27', plain,
% 0.60/0.81      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.81         ((k3_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.60/0.81           = (k4_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9))),
% 0.60/0.81      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.60/0.81  thf(t100_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.60/0.81  thf('28', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((k4_xboole_0 @ X0 @ X1)
% 0.60/0.81           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.81  thf('29', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.81         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.60/0.81           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 0.60/0.81      inference('sup+', [status(thm)], ['27', '28'])).
% 0.60/0.81  thf('30', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 0.60/0.81           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.81      inference('sup+', [status(thm)], ['26', '29'])).
% 0.60/0.81  thf(t22_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.60/0.81  thf('31', plain,
% 0.60/0.81      (![X5 : $i, X6 : $i]:
% 0.60/0.81         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 0.60/0.81      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.60/0.81  thf('32', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 0.60/0.81      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.81  thf('33', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.60/0.81      inference('demod', [status(thm)], ['25', '32'])).
% 0.60/0.81  thf('34', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['22', '33'])).
% 0.60/0.81  thf('35', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.60/0.81      inference('sup+', [status(thm)], ['1', '34'])).
% 0.60/0.81  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.60/0.81  
% 0.60/0.81  % SZS output end Refutation
% 0.60/0.81  
% 0.60/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
