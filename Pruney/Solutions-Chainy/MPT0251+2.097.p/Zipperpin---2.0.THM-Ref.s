%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pe66QbAelB

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:14 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  369 ( 538 expanded)
%              Number of equality atoms :   43 (  62 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('7',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k1_tarski @ X44 ) )
        = ( k1_tarski @ X44 ) )
      | ~ ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['14','15','16','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('30',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['20','30'])).

thf('32',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pe66QbAelB
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:35:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 192 iterations in 0.120s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(t21_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.37/0.56  thf(t100_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X4 @ X5)
% 0.37/0.56           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.37/0.56           = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf(t46_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.37/0.56  thf('4', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf(commutativity_k5_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf(t46_zfmisc_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.56       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i]:
% 0.37/0.56        ( ( r2_hidden @ A @ B ) =>
% 0.37/0.56          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.37/0.56  thf('6', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(l31_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.56       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X44 : $i, X45 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X45 @ (k1_tarski @ X44)) = (k1_tarski @ X44))
% 0.37/0.56          | ~ (r2_hidden @ X44 @ X45))),
% 0.37/0.56      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X4 @ X5)
% 0.37/0.56           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.37/0.56         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf(t91_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.37/0.56           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.37/0.56           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.37/0.56           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['5', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.37/0.56         (k1_tarski @ sk_A)) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['4', '13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf(t5_boole, axiom,
% 0.37/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.56  thf('18', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.56  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.37/0.56         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['14', '15', '16', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.56  thf(t94_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k2_xboole_0 @ A @ B ) =
% 0.37/0.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ X14 @ X15)
% 0.37/0.56           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.37/0.56              (k3_xboole_0 @ X14 @ X15)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ X14 @ X15)
% 0.37/0.56           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.37/0.56              (k5_xboole_0 @ X14 @ X15)))),
% 0.37/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.56           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['22', '25'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.37/0.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.37/0.56            (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['21', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.37/0.56         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.37/0.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.37/0.56            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.37/0.56  thf('31', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['20', '30'])).
% 0.37/0.56  thf('32', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('33', plain, ($false),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
