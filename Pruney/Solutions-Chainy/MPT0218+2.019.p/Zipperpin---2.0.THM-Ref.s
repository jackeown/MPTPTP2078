%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0s0wVGCFBE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  271 ( 301 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0s0wVGCFBE
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 24 iterations in 0.019s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.46  thf(t12_zfmisc_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t12_zfmisc_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t70_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X13 : $i, X14 : $i]:
% 0.19/0.46         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.19/0.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.46  thf(t73_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.46     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.19/0.46       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.46         ((k4_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.19/0.46           = (k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 0.19/0.46      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X13 : $i, X14 : $i]:
% 0.19/0.46         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.19/0.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.46  thf(t69_enumset1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.46  thf('4', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.19/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf(t71_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X15 @ X15 @ X16 @ X17)
% 0.19/0.46           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.46  thf(t72_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.46         ((k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21)
% 0.19/0.46           = (k2_enumset1 @ X18 @ X19 @ X20 @ X21))),
% 0.19/0.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.19/0.46  thf(t55_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.46     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.19/0.46       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.46         ((k4_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.19/0.46           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10) @ 
% 0.19/0.46              (k1_tarski @ X11)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.19/0.46  thf(t7_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.46         (r1_tarski @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.19/0.46          (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.46         (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.19/0.46          (k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 0.19/0.46      inference('sup+', [status(thm)], ['7', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.19/0.46          (k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 0.19/0.46      inference('sup+', [status(thm)], ['6', '11'])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (r1_tarski @ (k1_tarski @ X0) @ 
% 0.19/0.46          (k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1))),
% 0.19/0.46      inference('sup+', [status(thm)], ['5', '12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (r1_tarski @ (k1_tarski @ X1) @ (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['2', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.46         ((k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21)
% 0.19/0.46           = (k2_enumset1 @ X18 @ X19 @ X20 @ X21))),
% 0.19/0.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X15 @ X15 @ X16 @ X17)
% 0.19/0.46           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['1', '17'])).
% 0.19/0.46  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
