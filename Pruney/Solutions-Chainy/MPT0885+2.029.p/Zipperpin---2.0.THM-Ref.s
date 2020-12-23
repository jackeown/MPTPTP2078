%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kj9e112MbN

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:31 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  436 ( 466 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t45_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X5 @ X6 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('3',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X18 @ X21 ) @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X18 @ X19 ) @ ( k4_tarski @ X18 @ X20 ) @ ( k4_tarski @ X21 @ X19 ) @ ( k4_tarski @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['3','12','13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kj9e112MbN
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:10:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.07/1.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.29  % Solved by: fo/fo7.sh
% 1.07/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.29  % done 1322 iterations in 0.853s
% 1.07/1.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.29  % SZS output start Refutation
% 1.07/1.29  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.07/1.29  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.07/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.29  thf(sk_E_type, type, sk_E: $i).
% 1.07/1.29  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.07/1.29  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.07/1.29  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.29  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.07/1.29  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.29  thf(t45_mcart_1, conjecture,
% 1.07/1.29    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.07/1.29     ( ( k3_zfmisc_1 @
% 1.07/1.29         ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 1.07/1.29       ( k2_enumset1 @
% 1.07/1.29         ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 1.07/1.29         ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ))).
% 1.07/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.29    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.07/1.29        ( ( k3_zfmisc_1 @
% 1.07/1.29            ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 1.07/1.29          ( k2_enumset1 @
% 1.07/1.29            ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 1.07/1.29            ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )),
% 1.07/1.29    inference('cnf.neg', [status(esa)], [t45_mcart_1])).
% 1.07/1.29  thf('0', plain,
% 1.07/1.29      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 1.07/1.29         (k2_tarski @ sk_D @ sk_E))
% 1.07/1.29         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 1.07/1.29             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.29             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 1.07/1.29             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf(t105_enumset1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.29     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 1.07/1.29  thf('1', plain,
% 1.07/1.29      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.29         ((k2_enumset1 @ X4 @ X7 @ X5 @ X6) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 1.07/1.29      inference('cnf', [status(esa)], [t105_enumset1])).
% 1.07/1.29  thf(t103_enumset1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.29     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 1.07/1.29  thf('2', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.07/1.29         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 1.07/1.29      inference('cnf', [status(esa)], [t103_enumset1])).
% 1.07/1.29  thf('3', plain,
% 1.07/1.29      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 1.07/1.29         (k2_tarski @ sk_D @ sk_E))
% 1.07/1.29         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 1.07/1.29             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 1.07/1.29             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.29             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 1.07/1.29      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.07/1.29  thf(d3_mcart_1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.07/1.29  thf('4', plain,
% 1.07/1.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.07/1.29         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.07/1.29           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.07/1.29  thf('5', plain,
% 1.07/1.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.07/1.29         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.07/1.29           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.07/1.29  thf(t146_zfmisc_1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.29     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 1.07/1.29       ( k2_enumset1 @
% 1.07/1.29         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 1.07/1.29         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 1.07/1.29  thf('6', plain,
% 1.07/1.29      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.07/1.29         ((k2_zfmisc_1 @ (k2_tarski @ X18 @ X21) @ (k2_tarski @ X19 @ X20))
% 1.07/1.29           = (k2_enumset1 @ (k4_tarski @ X18 @ X19) @ 
% 1.07/1.29              (k4_tarski @ X18 @ X20) @ (k4_tarski @ X21 @ X19) @ 
% 1.07/1.29              (k4_tarski @ X21 @ X20)))),
% 1.07/1.29      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 1.07/1.29  thf('7', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.07/1.29         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 1.07/1.29           (k2_tarski @ X0 @ X3))
% 1.07/1.29           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.07/1.29              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 1.07/1.29              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 1.07/1.29      inference('sup+', [status(thm)], ['5', '6'])).
% 1.07/1.29  thf('8', plain,
% 1.07/1.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.07/1.29         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.07/1.29           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.07/1.29  thf('9', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.07/1.29         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 1.07/1.29           (k2_tarski @ X0 @ X3))
% 1.07/1.29           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.07/1.29              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 1.07/1.29              (k4_tarski @ X4 @ X3)))),
% 1.07/1.29      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.29  thf('10', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.07/1.29         ((k2_zfmisc_1 @ 
% 1.07/1.29           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 1.07/1.29           (k2_tarski @ X0 @ X3))
% 1.07/1.29           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 1.07/1.29              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.07/1.29              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 1.07/1.29      inference('sup+', [status(thm)], ['4', '9'])).
% 1.07/1.29  thf('11', plain,
% 1.07/1.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.07/1.29         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.07/1.29           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.07/1.29  thf('12', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.07/1.29         ((k2_zfmisc_1 @ 
% 1.07/1.29           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 1.07/1.29           (k2_tarski @ X0 @ X3))
% 1.07/1.29           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 1.07/1.29              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.07/1.29              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 1.07/1.29      inference('demod', [status(thm)], ['10', '11'])).
% 1.07/1.29  thf(t36_zfmisc_1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 1.07/1.29         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 1.07/1.29       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 1.07/1.29         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 1.07/1.29  thf('13', plain,
% 1.07/1.29      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.07/1.29         ((k2_zfmisc_1 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24))
% 1.07/1.29           = (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X22 @ X24)))),
% 1.07/1.29      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 1.07/1.29  thf(d3_zfmisc_1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.07/1.29       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.07/1.29  thf('14', plain,
% 1.07/1.29      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.07/1.29         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.07/1.29           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.07/1.29  thf('15', plain,
% 1.07/1.29      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 1.07/1.29         (k2_tarski @ sk_D @ sk_E))
% 1.07/1.29         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 1.07/1.29             (k2_tarski @ sk_D @ sk_E)))),
% 1.07/1.29      inference('demod', [status(thm)], ['3', '12', '13', '14'])).
% 1.07/1.29  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 1.07/1.29  
% 1.07/1.29  % SZS output end Refutation
% 1.07/1.29  
% 1.07/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
