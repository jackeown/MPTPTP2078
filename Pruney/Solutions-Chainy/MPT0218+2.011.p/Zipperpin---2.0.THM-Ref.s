%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bJ21Ynglyr

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  60 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  450 ( 510 expanded)
%              Number of equality atoms :   30 (  35 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k5_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bJ21Ynglyr
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 76 iterations in 0.067s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.52                                           $i > $i).
% 0.21/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(t12_zfmisc_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t70_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf(t69_enumset1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.52  thf('3', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(t75_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.52         ((k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.21/0.52           = (k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 0.21/0.52      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.21/0.52  thf(t74_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.52     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.52       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.21/0.52           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.21/0.52      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.52           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t73_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.52     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.52       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.52         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.21/0.52           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.21/0.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.52           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf(t72_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.21/0.52           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.52           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf(t68_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 0.21/0.52         X16 : $i]:
% 0.21/0.52         ((k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.21/0.52           = (k2_xboole_0 @ 
% 0.21/0.52              (k5_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 0.21/0.52              (k1_tarski @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.21/0.52  thf(t46_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.52  thf(l32_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (r1_tarski @ (k5_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.21/0.52          (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['12', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (r1_tarski @ (k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1) @ 
% 0.21/0.52          (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['11', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.21/0.52           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.21/0.52      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.52         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.21/0.52           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.21/0.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.21/0.52           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.52  thf(t71_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.21/0.52           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (r1_tarski @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.21/0.52          (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k1_tarski @ X0) @ (k2_enumset1 @ X0 @ X0 @ X0 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['4', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.21/0.52           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k1_tarski @ X0) @ (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['1', '26'])).
% 0.21/0.52  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
