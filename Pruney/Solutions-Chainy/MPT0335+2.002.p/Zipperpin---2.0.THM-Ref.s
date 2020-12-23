%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vEo7GWBRt7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:12 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   47 (  78 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  316 ( 641 expanded)
%              Number of equality atoms :   37 (  75 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12','13'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('23',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ X38 @ ( k1_tarski @ X37 ) )
        = ( k1_tarski @ X37 ) )
      | ~ ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_zfmisc_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['19','20','21','24'])).

thf('26',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vEo7GWBRt7
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:34:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.57  % Solved by: fo/fo7.sh
% 0.41/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.57  % done 273 iterations in 0.117s
% 0.41/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.57  % SZS output start Refutation
% 0.41/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.57  thf(t148_zfmisc_1, conjecture,
% 0.41/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.57     ( ( ( r1_tarski @ A @ B ) & 
% 0.41/0.57         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.41/0.57         ( r2_hidden @ D @ A ) ) =>
% 0.41/0.57       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.41/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.57        ( ( ( r1_tarski @ A @ B ) & 
% 0.41/0.57            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.41/0.57            ( r2_hidden @ D @ A ) ) =>
% 0.41/0.57          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.41/0.57    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.41/0.57  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t47_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.41/0.57  thf('1', plain,
% 0.41/0.57      (![X18 : $i, X19 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.41/0.57           = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.41/0.57  thf('2', plain,
% 0.41/0.57      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.41/0.57  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t28_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.57  thf('4', plain,
% 0.41/0.57      (![X16 : $i, X17 : $i]:
% 0.41/0.57         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.41/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.57  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.41/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.57  thf('6', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.57  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.41/0.57  thf(t111_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.41/0.57       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.41/0.57  thf('8', plain,
% 0.41/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ (k3_xboole_0 @ X11 @ X13) @ (k3_xboole_0 @ X12 @ X13))
% 0.41/0.57           = (k3_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13))),
% 0.41/0.57      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.41/0.57  thf('9', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_A))
% 0.41/0.57           = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.41/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.57  thf('10', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.57  thf('11', plain,
% 0.41/0.57      (![X18 : $i, X19 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.41/0.57           = (k4_xboole_0 @ X18 @ X19))),
% 0.41/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.41/0.57  thf('12', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.57           = (k4_xboole_0 @ X0 @ X1))),
% 0.41/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.57  thf('13', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.57  thf('14', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ sk_A @ X0)
% 0.41/0.57           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.41/0.57      inference('demod', [status(thm)], ['9', '12', '13'])).
% 0.41/0.57  thf('15', plain,
% 0.41/0.57      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D))
% 0.41/0.57         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.57      inference('sup+', [status(thm)], ['2', '14'])).
% 0.41/0.57  thf('16', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ sk_A @ X0)
% 0.41/0.57           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.41/0.57      inference('demod', [status(thm)], ['9', '12', '13'])).
% 0.41/0.57  thf('17', plain,
% 0.41/0.57      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.41/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.41/0.57  thf(t48_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.57  thf('18', plain,
% 0.41/0.57      (![X20 : $i, X21 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.41/0.57           = (k3_xboole_0 @ X20 @ X21))),
% 0.41/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.57  thf('19', plain,
% 0.41/0.57      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.41/0.57         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.41/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.41/0.57  thf('20', plain,
% 0.41/0.57      (![X20 : $i, X21 : $i]:
% 0.41/0.57         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.41/0.57           = (k3_xboole_0 @ X20 @ X21))),
% 0.41/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.57  thf('21', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.57  thf('22', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t52_zfmisc_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.41/0.57       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.41/0.57  thf('23', plain,
% 0.41/0.57      (![X37 : $i, X38 : $i]:
% 0.41/0.57         (((k3_xboole_0 @ X38 @ (k1_tarski @ X37)) = (k1_tarski @ X37))
% 0.41/0.57          | ~ (r2_hidden @ X37 @ X38))),
% 0.41/0.57      inference('cnf', [status(esa)], [t52_zfmisc_1])).
% 0.41/0.57  thf('24', plain,
% 0.41/0.57      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.41/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.57  thf('25', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 0.41/0.57      inference('demod', [status(thm)], ['19', '20', '21', '24'])).
% 0.41/0.57  thf('26', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('27', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.57  thf('28', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.41/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.41/0.57  thf('29', plain, ($false),
% 0.41/0.57      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 0.41/0.57  
% 0.41/0.57  % SZS output end Refutation
% 0.41/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
