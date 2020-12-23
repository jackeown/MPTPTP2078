%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xHW7DFQCrY

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:15 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  358 ( 671 expanded)
%              Number of equality atoms :   41 (  78 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ X33 @ X32 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X31 @ X33 ) @ X32 )
        = ( k2_tarski @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_D @ X0 ) @ sk_A )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D @ X0 ) )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D @ sk_D ) )
    = ( k2_tarski @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['16','17','18','28'])).

thf('30',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xHW7DFQCrY
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:23:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.76/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/1.00  % Solved by: fo/fo7.sh
% 0.76/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/1.00  % done 1757 iterations in 0.536s
% 0.76/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/1.00  % SZS output start Refutation
% 0.76/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/1.00  thf(sk_C_type, type, sk_C: $i).
% 0.76/1.00  thf(sk_D_type, type, sk_D: $i).
% 0.76/1.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.76/1.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/1.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.76/1.00  thf(t148_zfmisc_1, conjecture,
% 0.76/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.00     ( ( ( r1_tarski @ A @ B ) & 
% 0.76/1.00         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.76/1.00         ( r2_hidden @ D @ A ) ) =>
% 0.76/1.00       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.76/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.76/1.00    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.00        ( ( ( r1_tarski @ A @ B ) & 
% 0.76/1.00            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.76/1.00            ( r2_hidden @ D @ A ) ) =>
% 0.76/1.00          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.76/1.00    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.76/1.00  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(t47_xboole_1, axiom,
% 0.76/1.00    (![A:$i,B:$i]:
% 0.76/1.00     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/1.00  thf('1', plain,
% 0.76/1.00      (![X14 : $i, X15 : $i]:
% 0.76/1.00         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.76/1.00           = (k4_xboole_0 @ X14 @ X15))),
% 0.76/1.00      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/1.00  thf('2', plain,
% 0.76/1.00      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.76/1.00      inference('sup+', [status(thm)], ['0', '1'])).
% 0.76/1.00  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(t28_xboole_1, axiom,
% 0.76/1.00    (![A:$i,B:$i]:
% 0.76/1.00     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.76/1.00  thf('4', plain,
% 0.76/1.00      (![X11 : $i, X12 : $i]:
% 0.76/1.00         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.76/1.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.76/1.00  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.76/1.00      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/1.00  thf(commutativity_k3_xboole_0, axiom,
% 0.76/1.00    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/1.00  thf('6', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.00  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.76/1.00      inference('demod', [status(thm)], ['5', '6'])).
% 0.76/1.00  thf('8', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.00  thf(t49_xboole_1, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.76/1.00       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.76/1.00  thf('9', plain,
% 0.76/1.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.76/1.00         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.76/1.00           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.76/1.00      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.76/1.00  thf('10', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.00         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.76/1.00           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.76/1.00      inference('sup+', [status(thm)], ['8', '9'])).
% 0.76/1.00  thf('11', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.76/1.00           = (k4_xboole_0 @ sk_A @ X0))),
% 0.76/1.00      inference('sup+', [status(thm)], ['7', '10'])).
% 0.76/1.00  thf('12', plain,
% 0.76/1.00      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.76/1.00         = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.76/1.00      inference('sup+', [status(thm)], ['2', '11'])).
% 0.76/1.00  thf('13', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.76/1.00           = (k4_xboole_0 @ sk_A @ X0))),
% 0.76/1.00      inference('sup+', [status(thm)], ['7', '10'])).
% 0.76/1.00  thf('14', plain,
% 0.76/1.00      (((k4_xboole_0 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.76/1.00      inference('demod', [status(thm)], ['12', '13'])).
% 0.76/1.00  thf(t48_xboole_1, axiom,
% 0.76/1.00    (![A:$i,B:$i]:
% 0.76/1.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/1.00  thf('15', plain,
% 0.76/1.00      (![X16 : $i, X17 : $i]:
% 0.76/1.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.76/1.00           = (k3_xboole_0 @ X16 @ X17))),
% 0.76/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/1.00  thf('16', plain,
% 0.76/1.00      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.76/1.00         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.76/1.00      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/1.00  thf('17', plain,
% 0.76/1.00      (![X16 : $i, X17 : $i]:
% 0.76/1.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.76/1.00           = (k3_xboole_0 @ X16 @ X17))),
% 0.76/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/1.00  thf('18', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.00  thf('19', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('20', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(t53_zfmisc_1, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.76/1.00       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.76/1.00  thf('21', plain,
% 0.76/1.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.76/1.00         (~ (r2_hidden @ X31 @ X32)
% 0.76/1.00          | ~ (r2_hidden @ X33 @ X32)
% 0.76/1.00          | ((k3_xboole_0 @ (k2_tarski @ X31 @ X33) @ X32)
% 0.76/1.00              = (k2_tarski @ X31 @ X33)))),
% 0.76/1.00      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 0.76/1.00  thf('22', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         (((k3_xboole_0 @ (k2_tarski @ sk_D @ X0) @ sk_A)
% 0.76/1.00            = (k2_tarski @ sk_D @ X0))
% 0.76/1.00          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.76/1.00      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/1.00  thf('23', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.00  thf('24', plain,
% 0.76/1.00      (![X0 : $i]:
% 0.76/1.00         (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D @ X0))
% 0.76/1.00            = (k2_tarski @ sk_D @ X0))
% 0.76/1.00          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.76/1.00      inference('demod', [status(thm)], ['22', '23'])).
% 0.76/1.00  thf('25', plain,
% 0.76/1.00      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D @ sk_D))
% 0.76/1.00         = (k2_tarski @ sk_D @ sk_D))),
% 0.76/1.00      inference('sup-', [status(thm)], ['19', '24'])).
% 0.76/1.00  thf(t69_enumset1, axiom,
% 0.76/1.00    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.76/1.00  thf('26', plain,
% 0.76/1.00      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.76/1.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.76/1.00  thf('27', plain,
% 0.76/1.00      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.76/1.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.76/1.00  thf('28', plain,
% 0.76/1.00      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.76/1.00  thf('29', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['16', '17', '18', '28'])).
% 0.76/1.00  thf('30', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('31', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/1.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/1.00  thf('32', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.76/1.00      inference('demod', [status(thm)], ['30', '31'])).
% 0.76/1.00  thf('33', plain, ($false),
% 0.76/1.00      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 0.76/1.00  
% 0.76/1.00  % SZS output end Refutation
% 0.76/1.00  
% 0.84/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
