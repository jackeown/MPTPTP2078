%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EtPH82Fjae

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  279 ( 293 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t81_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) ),
    inference('cnf.neg',[status(esa)],[t81_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X39 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k4_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('3',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k4_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EtPH82Fjae
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 17 iterations in 0.017s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.47                                           $i > $i).
% 0.20/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(t81_enumset1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.47     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.47       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.47        ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.47          ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t81_enumset1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.20/0.47         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t79_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.20/0.47       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.47         ((k4_enumset1 @ X39 @ X39 @ X39 @ X40 @ X41 @ X42)
% 0.20/0.47           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 0.20/0.47      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.20/0.47  thf(t73_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.47       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.47         ((k4_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38)
% 0.20/0.47           = (k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38))),
% 0.20/0.47      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.47         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 0.20/0.47           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 0.20/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.47         ((k4_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38)
% 0.20/0.47           = (k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38))),
% 0.20/0.47      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.47  thf(t67_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.47     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.47       ( k2_xboole_0 @
% 0.20/0.47         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, 
% 0.20/0.47         X33 : $i]:
% 0.20/0.47         ((k6_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.20/0.47           = (k2_xboole_0 @ 
% 0.20/0.47              (k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31) @ 
% 0.20/0.47              (k2_tarski @ X32 @ X33)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 0.20/0.47           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.20/0.47              (k2_tarski @ X6 @ X5)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((k6_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.20/0.47           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.20/0.47              (k2_tarski @ X5 @ X4)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.47  thf(t54_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.47     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.47         ((k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.47           = (k2_xboole_0 @ (k2_enumset1 @ X14 @ X15 @ X16 @ X17) @ 
% 0.20/0.47              (k2_tarski @ X18 @ X19)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((k6_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.20/0.47           = (k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.20/0.47         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '9'])).
% 0.20/0.47  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
