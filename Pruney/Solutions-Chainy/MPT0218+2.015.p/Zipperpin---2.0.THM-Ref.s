%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONzOuoQiLl

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:02 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   61 (  63 expanded)
%              Number of leaves         :   29 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  467 ( 484 expanded)
%              Number of equality atoms :   32 (  34 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('7',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t64_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X14 @ X15 @ X16 ) @ ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t64_enumset1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k6_enumset1 @ X0 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_tarski @ ( k1_tarski @ X5 ) @ ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','24'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_tarski @ ( k1_tarski @ X5 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONzOuoQiLl
% 0.12/0.35  % Computer   : n001.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 11:20:15 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.35/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.59  % Solved by: fo/fo7.sh
% 0.35/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.59  % done 173 iterations in 0.132s
% 0.35/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.59  % SZS output start Refutation
% 0.35/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.35/0.59  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.35/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.59  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.35/0.59                                           $i > $i).
% 0.35/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.35/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.59  thf(t12_zfmisc_1, conjecture,
% 0.35/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.35/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.59    (~( ![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )),
% 0.35/0.59    inference('cnf.neg', [status(esa)], [t12_zfmisc_1])).
% 0.35/0.59  thf('0', plain,
% 0.35/0.59      (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(t71_enumset1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i]:
% 0.35/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.35/0.59  thf('1', plain,
% 0.35/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.35/0.59         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 0.35/0.59           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.35/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.35/0.59  thf(t70_enumset1, axiom,
% 0.35/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.35/0.59  thf('2', plain,
% 0.35/0.59      (![X23 : $i, X24 : $i]:
% 0.35/0.59         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.35/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.59  thf('3', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.35/0.59  thf(t73_enumset1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.35/0.59     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.35/0.59       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.35/0.59  thf('4', plain,
% 0.35/0.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.35/0.59         ((k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.35/0.59           = (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.35/0.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.35/0.59  thf(t72_enumset1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.59     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.35/0.59  thf('5', plain,
% 0.35/0.59      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.35/0.59         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 0.35/0.59           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 0.35/0.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.35/0.59  thf('6', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.59         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.35/0.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.35/0.59  thf(t75_enumset1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.35/0.59     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.35/0.59       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.35/0.59  thf('7', plain,
% 0.35/0.59      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.35/0.59         ((k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.35/0.59           = (k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.35/0.59      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.35/0.59  thf('8', plain,
% 0.35/0.59      (![X23 : $i, X24 : $i]:
% 0.35/0.59         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.35/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.59  thf(t69_enumset1, axiom,
% 0.35/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.59  thf('9', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.35/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.59  thf('10', plain,
% 0.35/0.59      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['8', '9'])).
% 0.35/0.59  thf(t64_enumset1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.35/0.59     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.35/0.59       ( k2_xboole_0 @
% 0.35/0.59         ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ))).
% 0.35/0.59  thf('11', plain,
% 0.35/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.35/0.59         X21 : $i]:
% 0.35/0.59         ((k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.35/0.59           = (k2_xboole_0 @ (k1_enumset1 @ X14 @ X15 @ X16) @ 
% 0.35/0.59              (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t64_enumset1])).
% 0.35/0.59  thf(t98_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.35/0.59  thf('12', plain,
% 0.35/0.59      (![X12 : $i, X13 : $i]:
% 0.35/0.59         ((k2_xboole_0 @ X12 @ X13)
% 0.35/0.59           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.59  thf(t96_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.35/0.59  thf('13', plain,
% 0.35/0.59      (![X10 : $i, X11 : $i]:
% 0.35/0.59         (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ (k5_xboole_0 @ X10 @ X11))),
% 0.35/0.59      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.35/0.59  thf('14', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (r1_tarski @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 0.35/0.59          (k2_xboole_0 @ X1 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.35/0.59  thf('15', plain,
% 0.35/0.59      (![X12 : $i, X13 : $i]:
% 0.35/0.59         ((k2_xboole_0 @ X12 @ X13)
% 0.35/0.59           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.59  thf(t49_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i]:
% 0.35/0.59     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.35/0.59       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.35/0.59  thf('16', plain,
% 0.35/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.59         ((k3_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.35/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9))),
% 0.35/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.35/0.59  thf(t100_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.59  thf('17', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.35/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.59  thf('18', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.35/0.59           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.35/0.59  thf('19', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 0.35/0.59           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['15', '18'])).
% 0.35/0.59  thf(t22_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.35/0.59  thf('20', plain,
% 0.35/0.59      (![X5 : $i, X6 : $i]:
% 0.35/0.59         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 0.35/0.59      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.35/0.59  thf('21', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 0.35/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.59  thf('22', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.35/0.59      inference('demod', [status(thm)], ['14', '21'])).
% 0.35/0.59  thf('23', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.59         (r1_tarski @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.35/0.59          (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['11', '22'])).
% 0.35/0.59  thf('24', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.59         (r1_tarski @ (k1_tarski @ X0) @ 
% 0.35/0.59          (k6_enumset1 @ X0 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1))),
% 0.35/0.59      inference('sup+', [status(thm)], ['10', '23'])).
% 0.35/0.59  thf('25', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.59         (r1_tarski @ (k1_tarski @ X5) @ 
% 0.35/0.59          (k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['7', '24'])).
% 0.35/0.59  thf(t74_enumset1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.59     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.35/0.59       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.35/0.59  thf('26', plain,
% 0.35/0.59      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.35/0.59         ((k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.35/0.59           = (k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.35/0.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.35/0.59  thf('27', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.59         (r1_tarski @ (k1_tarski @ X5) @ 
% 0.35/0.59          (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.35/0.59  thf('28', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.59         (r1_tarski @ (k1_tarski @ X3) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['6', '27'])).
% 0.35/0.59  thf('29', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['3', '28'])).
% 0.35/0.59  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.35/0.59  
% 0.35/0.59  % SZS output end Refutation
% 0.35/0.59  
% 0.35/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
