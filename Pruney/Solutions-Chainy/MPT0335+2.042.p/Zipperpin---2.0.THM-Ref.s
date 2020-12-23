%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FPJBTTf5ab

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:18 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 ( 493 expanded)
%              Number of equality atoms :   32 (  55 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X35: $i,X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X35 @ X37 ) @ X38 )
      | ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r2_hidden @ X35 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_tarski @ sk_D @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf('28',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FPJBTTf5ab
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 137 iterations in 0.174s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf(t148_zfmisc_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ B ) & 
% 0.39/0.62         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.39/0.62         ( r2_hidden @ D @ A ) ) =>
% 0.39/0.62       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62        ( ( ( r1_tarski @ A @ B ) & 
% 0.39/0.62            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.39/0.62            ( r2_hidden @ D @ A ) ) =>
% 0.39/0.62          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.39/0.62  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t28_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.63  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.39/0.63      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.63  thf(t16_xboole_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.63       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.63  thf('6', plain,
% 0.39/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.63         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.39/0.63           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.39/0.63  thf('7', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((k3_xboole_0 @ sk_A @ X0)
% 0.39/0.63           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.39/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.39/0.63  thf('8', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((k3_xboole_0 @ sk_A @ X0)
% 0.39/0.63           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.39/0.63      inference('sup+', [status(thm)], ['0', '7'])).
% 0.39/0.63  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('10', plain,
% 0.39/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.63         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.39/0.63           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.39/0.63  thf('11', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.39/0.63           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.39/0.63      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.63  thf('12', plain,
% 0.39/0.63      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.63      inference('sup+', [status(thm)], ['8', '11'])).
% 0.39/0.63  thf('13', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.63  thf('14', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.63  thf('15', plain,
% 0.39/0.63      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.39/0.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.39/0.63  thf('16', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('17', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(t38_zfmisc_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.39/0.63       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.39/0.63  thf('18', plain,
% 0.39/0.63      (![X35 : $i, X37 : $i, X38 : $i]:
% 0.39/0.63         ((r1_tarski @ (k2_tarski @ X35 @ X37) @ X38)
% 0.39/0.63          | ~ (r2_hidden @ X37 @ X38)
% 0.39/0.63          | ~ (r2_hidden @ X35 @ X38))),
% 0.39/0.63      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.39/0.63  thf('19', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.39/0.63          | (r1_tarski @ (k2_tarski @ X0 @ sk_D) @ sk_A))),
% 0.39/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.63  thf('20', plain, ((r1_tarski @ (k2_tarski @ sk_D @ sk_D) @ sk_A)),
% 0.39/0.63      inference('sup-', [status(thm)], ['16', '19'])).
% 0.39/0.63  thf(t69_enumset1, axiom,
% 0.39/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.63  thf('21', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.39/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.63  thf('22', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_A)),
% 0.39/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.39/0.63  thf('23', plain,
% 0.39/0.63      (![X5 : $i, X6 : $i]:
% 0.39/0.63         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.39/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.63  thf('24', plain,
% 0.39/0.63      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_tarski @ sk_D))),
% 0.39/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.63  thf('25', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.63  thf('26', plain,
% 0.39/0.63      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.39/0.63      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.63  thf('27', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 0.39/0.63      inference('sup+', [status(thm)], ['15', '26'])).
% 0.39/0.63  thf('28', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('29', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.63  thf('30', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.39/0.63      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.63  thf('31', plain, ($false),
% 0.39/0.63      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
