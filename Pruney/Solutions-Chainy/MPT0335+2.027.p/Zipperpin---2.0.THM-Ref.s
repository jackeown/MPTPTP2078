%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9sPgUsY1le

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:16 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  329 ( 525 expanded)
%              Number of equality atoms :   39 (  62 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( r2_hidden @ X36 @ X35 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X34 @ X36 ) @ X35 )
        = ( k2_tarski @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_D_1 @ X0 ) @ sk_A )
        = ( k2_tarski @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D_1 @ X0 ) )
        = ( k2_tarski @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_D_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['17','27'])).

thf('29',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9sPgUsY1le
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:35:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.50/1.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.74  % Solved by: fo/fo7.sh
% 1.50/1.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.74  % done 1900 iterations in 1.275s
% 1.50/1.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.74  % SZS output start Refutation
% 1.50/1.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.74  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.50/1.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.50/1.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.50/1.74  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.50/1.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.50/1.74  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.50/1.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.74  thf(commutativity_k3_xboole_0, axiom,
% 1.50/1.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.50/1.74  thf('0', plain,
% 1.50/1.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.74  thf(t148_zfmisc_1, conjecture,
% 1.50/1.74    (![A:$i,B:$i,C:$i,D:$i]:
% 1.50/1.74     ( ( ( r1_tarski @ A @ B ) & 
% 1.50/1.74         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.50/1.74         ( r2_hidden @ D @ A ) ) =>
% 1.50/1.74       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.50/1.74  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.50/1.74        ( ( ( r1_tarski @ A @ B ) & 
% 1.50/1.74            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.50/1.74            ( r2_hidden @ D @ A ) ) =>
% 1.50/1.74          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.50/1.74    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.50/1.74  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.50/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.74  thf(t12_xboole_1, axiom,
% 1.50/1.74    (![A:$i,B:$i]:
% 1.50/1.74     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.50/1.74  thf('2', plain,
% 1.50/1.74      (![X12 : $i, X13 : $i]:
% 1.50/1.74         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.50/1.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.50/1.74  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.50/1.74      inference('sup-', [status(thm)], ['1', '2'])).
% 1.50/1.74  thf(t21_xboole_1, axiom,
% 1.50/1.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.50/1.74  thf('4', plain,
% 1.50/1.74      (![X17 : $i, X18 : $i]:
% 1.50/1.74         ((k3_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (X17))),
% 1.50/1.74      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.50/1.74  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.50/1.74      inference('sup+', [status(thm)], ['3', '4'])).
% 1.50/1.74  thf('6', plain,
% 1.50/1.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.74  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 1.50/1.74      inference('demod', [status(thm)], ['5', '6'])).
% 1.50/1.74  thf(t16_xboole_1, axiom,
% 1.50/1.74    (![A:$i,B:$i,C:$i]:
% 1.50/1.74     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.50/1.74       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.50/1.74  thf('8', plain,
% 1.50/1.74      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.50/1.74         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 1.50/1.74           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.50/1.74      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.50/1.74  thf('9', plain,
% 1.50/1.74      (![X0 : $i]:
% 1.50/1.74         ((k3_xboole_0 @ sk_A @ X0)
% 1.50/1.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.50/1.74      inference('sup+', [status(thm)], ['7', '8'])).
% 1.50/1.74  thf('10', plain,
% 1.50/1.74      (![X0 : $i]:
% 1.50/1.74         ((k3_xboole_0 @ sk_A @ X0)
% 1.50/1.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 1.50/1.74      inference('sup+', [status(thm)], ['0', '9'])).
% 1.50/1.74  thf('11', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.50/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.74  thf('12', plain,
% 1.50/1.74      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.50/1.74         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 1.50/1.74           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.50/1.74      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.50/1.74  thf('13', plain,
% 1.50/1.74      (![X0 : $i]:
% 1.50/1.74         ((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)
% 1.50/1.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.50/1.74      inference('sup+', [status(thm)], ['11', '12'])).
% 1.50/1.74  thf('14', plain,
% 1.50/1.74      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A)
% 1.50/1.74         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 1.50/1.74      inference('sup+', [status(thm)], ['10', '13'])).
% 1.50/1.74  thf('15', plain,
% 1.50/1.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.74  thf('16', plain,
% 1.50/1.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.74  thf('17', plain,
% 1.50/1.74      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 1.50/1.74         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.50/1.74      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.50/1.74  thf('18', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.50/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.74  thf('19', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.50/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.74  thf(t53_zfmisc_1, axiom,
% 1.50/1.74    (![A:$i,B:$i,C:$i]:
% 1.50/1.74     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.50/1.74       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 1.50/1.74  thf('20', plain,
% 1.50/1.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.50/1.74         (~ (r2_hidden @ X34 @ X35)
% 1.50/1.74          | ~ (r2_hidden @ X36 @ X35)
% 1.50/1.74          | ((k3_xboole_0 @ (k2_tarski @ X34 @ X36) @ X35)
% 1.50/1.74              = (k2_tarski @ X34 @ X36)))),
% 1.50/1.74      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 1.50/1.74  thf('21', plain,
% 1.50/1.74      (![X0 : $i]:
% 1.50/1.74         (((k3_xboole_0 @ (k2_tarski @ sk_D_1 @ X0) @ sk_A)
% 1.50/1.74            = (k2_tarski @ sk_D_1 @ X0))
% 1.50/1.74          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.50/1.74      inference('sup-', [status(thm)], ['19', '20'])).
% 1.50/1.74  thf('22', plain,
% 1.50/1.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.74  thf('23', plain,
% 1.50/1.74      (![X0 : $i]:
% 1.50/1.74         (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D_1 @ X0))
% 1.50/1.74            = (k2_tarski @ sk_D_1 @ X0))
% 1.50/1.74          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.50/1.74      inference('demod', [status(thm)], ['21', '22'])).
% 1.50/1.74  thf('24', plain,
% 1.50/1.74      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D_1 @ sk_D_1))
% 1.50/1.74         = (k2_tarski @ sk_D_1 @ sk_D_1))),
% 1.50/1.74      inference('sup-', [status(thm)], ['18', '23'])).
% 1.50/1.74  thf(t69_enumset1, axiom,
% 1.50/1.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.50/1.74  thf('25', plain,
% 1.50/1.74      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 1.50/1.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.50/1.74  thf('26', plain,
% 1.50/1.74      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 1.50/1.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.50/1.74  thf('27', plain,
% 1.50/1.74      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 1.50/1.74      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.50/1.74  thf('28', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_tarski @ sk_D_1))),
% 1.50/1.74      inference('sup+', [status(thm)], ['17', '27'])).
% 1.50/1.74  thf('29', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 1.50/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.74  thf('30', plain,
% 1.50/1.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.74  thf('31', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D_1))),
% 1.50/1.74      inference('demod', [status(thm)], ['29', '30'])).
% 1.50/1.74  thf('32', plain, ($false),
% 1.50/1.74      inference('simplify_reflect-', [status(thm)], ['28', '31'])).
% 1.50/1.74  
% 1.50/1.74  % SZS output end Refutation
% 1.50/1.74  
% 1.50/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
