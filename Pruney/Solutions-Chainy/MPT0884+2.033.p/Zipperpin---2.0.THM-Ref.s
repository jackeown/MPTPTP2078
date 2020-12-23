%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VolalPx3Z3

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:27 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
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

thf(t44_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
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
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
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
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X22 @ X23 ) @ ( k1_tarski @ X25 ) )
      = ( k2_tarski @ ( k4_tarski @ X22 @ X25 ) @ ( k4_tarski @ X23 @ X25 ) ) ) ),
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
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['3','12','13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VolalPx3Z3
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.94/2.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.94/2.17  % Solved by: fo/fo7.sh
% 1.94/2.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.17  % done 1322 iterations in 1.715s
% 1.94/2.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.94/2.17  % SZS output start Refutation
% 1.94/2.17  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.94/2.17  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.94/2.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.94/2.17  thf(sk_B_type, type, sk_B: $i).
% 1.94/2.17  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.17  thf(sk_E_type, type, sk_E: $i).
% 1.94/2.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.94/2.17  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.94/2.17  thf(sk_C_type, type, sk_C: $i).
% 1.94/2.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.94/2.17  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.94/2.17  thf(sk_D_type, type, sk_D: $i).
% 1.94/2.17  thf(t44_mcart_1, conjecture,
% 1.94/2.17    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.94/2.17     ( ( k3_zfmisc_1 @
% 1.94/2.17         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 1.94/2.17       ( k2_enumset1 @
% 1.94/2.17         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 1.94/2.17         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 1.94/2.17  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.17    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.94/2.17        ( ( k3_zfmisc_1 @
% 1.94/2.17            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 1.94/2.17          ( k2_enumset1 @
% 1.94/2.17            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 1.94/2.17            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 1.94/2.17    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 1.94/2.17  thf('0', plain,
% 1.94/2.17      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 1.94/2.17         (k2_tarski @ sk_D @ sk_E))
% 1.94/2.17         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.94/2.17             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 1.94/2.17             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 1.94/2.17             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf(t105_enumset1, axiom,
% 1.94/2.17    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.17     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 1.94/2.17  thf('1', plain,
% 1.94/2.17      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.94/2.17         ((k2_enumset1 @ X4 @ X7 @ X5 @ X6) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 1.94/2.17      inference('cnf', [status(esa)], [t105_enumset1])).
% 1.94/2.17  thf(t103_enumset1, axiom,
% 1.94/2.17    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.17     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 1.94/2.17  thf('2', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.94/2.17         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 1.94/2.17      inference('cnf', [status(esa)], [t103_enumset1])).
% 1.94/2.17  thf('3', plain,
% 1.94/2.17      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 1.94/2.17         (k2_tarski @ sk_D @ sk_E))
% 1.94/2.17         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.94/2.17             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 1.94/2.17             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 1.94/2.17             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 1.94/2.17      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.94/2.17  thf(d3_mcart_1, axiom,
% 1.94/2.17    (![A:$i,B:$i,C:$i]:
% 1.94/2.17     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.94/2.17  thf('4', plain,
% 1.94/2.17      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.94/2.17         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.94/2.17           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.94/2.17      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.94/2.17  thf('5', plain,
% 1.94/2.17      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.94/2.17         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.94/2.17           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.94/2.17      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.94/2.17  thf(t146_zfmisc_1, axiom,
% 1.94/2.17    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.17     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 1.94/2.17       ( k2_enumset1 @
% 1.94/2.17         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 1.94/2.17         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 1.94/2.17  thf('6', plain,
% 1.94/2.17      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.94/2.17         ((k2_zfmisc_1 @ (k2_tarski @ X18 @ X21) @ (k2_tarski @ X19 @ X20))
% 1.94/2.17           = (k2_enumset1 @ (k4_tarski @ X18 @ X19) @ 
% 1.94/2.17              (k4_tarski @ X18 @ X20) @ (k4_tarski @ X21 @ X19) @ 
% 1.94/2.17              (k4_tarski @ X21 @ X20)))),
% 1.94/2.17      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 1.94/2.17  thf('7', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.94/2.17         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 1.94/2.17           (k2_tarski @ X0 @ X3))
% 1.94/2.17           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.94/2.17              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 1.94/2.17              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 1.94/2.17      inference('sup+', [status(thm)], ['5', '6'])).
% 1.94/2.17  thf('8', plain,
% 1.94/2.17      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.94/2.17         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.94/2.17           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.94/2.17      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.94/2.17  thf('9', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.94/2.17         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 1.94/2.17           (k2_tarski @ X0 @ X3))
% 1.94/2.17           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.94/2.17              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 1.94/2.17              (k4_tarski @ X4 @ X3)))),
% 1.94/2.17      inference('demod', [status(thm)], ['7', '8'])).
% 1.94/2.17  thf('10', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.94/2.17         ((k2_zfmisc_1 @ 
% 1.94/2.17           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 1.94/2.17           (k2_tarski @ X0 @ X3))
% 1.94/2.17           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 1.94/2.17              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.94/2.17              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 1.94/2.17      inference('sup+', [status(thm)], ['4', '9'])).
% 1.94/2.17  thf('11', plain,
% 1.94/2.17      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.94/2.17         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.94/2.17           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.94/2.17      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.94/2.17  thf('12', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.94/2.17         ((k2_zfmisc_1 @ 
% 1.94/2.17           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 1.94/2.17           (k2_tarski @ X0 @ X3))
% 1.94/2.17           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 1.94/2.17              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.94/2.17              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 1.94/2.17      inference('demod', [status(thm)], ['10', '11'])).
% 1.94/2.17  thf(t36_zfmisc_1, axiom,
% 1.94/2.17    (![A:$i,B:$i,C:$i]:
% 1.94/2.17     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 1.94/2.17         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 1.94/2.17       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 1.94/2.17         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 1.94/2.17  thf('13', plain,
% 1.94/2.17      (![X22 : $i, X23 : $i, X25 : $i]:
% 1.94/2.17         ((k2_zfmisc_1 @ (k2_tarski @ X22 @ X23) @ (k1_tarski @ X25))
% 1.94/2.17           = (k2_tarski @ (k4_tarski @ X22 @ X25) @ (k4_tarski @ X23 @ X25)))),
% 1.94/2.17      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 1.94/2.17  thf(d3_zfmisc_1, axiom,
% 1.94/2.17    (![A:$i,B:$i,C:$i]:
% 1.94/2.17     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.94/2.17       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.94/2.17  thf('14', plain,
% 1.94/2.17      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.94/2.17         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.94/2.17           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.94/2.17      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.94/2.17  thf('15', plain,
% 1.94/2.17      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 1.94/2.17         (k2_tarski @ sk_D @ sk_E))
% 1.94/2.17         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 1.94/2.17             (k2_tarski @ sk_D @ sk_E)))),
% 1.94/2.17      inference('demod', [status(thm)], ['3', '12', '13', '14'])).
% 1.94/2.17  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 1.94/2.17  
% 1.94/2.17  % SZS output end Refutation
% 1.94/2.17  
% 1.94/2.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
