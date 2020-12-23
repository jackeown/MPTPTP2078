%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u3vAcFu21A

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:18 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 ( 506 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X13 @ X15 ) @ X14 )
        = ( k2_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_D @ X0 ) @ sk_A )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D @ X0 ) )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D @ sk_D ) )
    = ( k2_tarski @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['15','25'])).

thf('27',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u3vAcFu21A
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.65/1.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.89  % Solved by: fo/fo7.sh
% 1.65/1.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.89  % done 291 iterations in 1.443s
% 1.65/1.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.89  % SZS output start Refutation
% 1.65/1.89  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.65/1.89  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.89  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.65/1.89  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.65/1.89  thf(commutativity_k3_xboole_0, axiom,
% 1.65/1.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.65/1.89  thf('0', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.89  thf(t148_zfmisc_1, conjecture,
% 1.65/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.89     ( ( ( r1_tarski @ A @ B ) & 
% 1.65/1.89         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.65/1.89         ( r2_hidden @ D @ A ) ) =>
% 1.65/1.89       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.65/1.89  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.89        ( ( ( r1_tarski @ A @ B ) & 
% 1.65/1.89            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.65/1.89            ( r2_hidden @ D @ A ) ) =>
% 1.65/1.89          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.65/1.89    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.65/1.89  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf(t28_xboole_1, axiom,
% 1.65/1.89    (![A:$i,B:$i]:
% 1.65/1.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.65/1.89  thf('2', plain,
% 1.65/1.89      (![X5 : $i, X6 : $i]:
% 1.65/1.89         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 1.65/1.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.65/1.89  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.65/1.89      inference('sup-', [status(thm)], ['1', '2'])).
% 1.65/1.89  thf('4', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.89  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['3', '4'])).
% 1.65/1.89  thf(t16_xboole_1, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i]:
% 1.65/1.89     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.65/1.89       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.65/1.89  thf('6', plain,
% 1.65/1.89      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 1.65/1.89           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.65/1.89  thf('7', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ sk_A @ X0)
% 1.65/1.89           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['5', '6'])).
% 1.65/1.89  thf('8', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ sk_A @ X0)
% 1.65/1.89           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['0', '7'])).
% 1.65/1.89  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('10', plain,
% 1.65/1.89      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 1.65/1.89           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.65/1.89  thf('11', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 1.65/1.89           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['9', '10'])).
% 1.65/1.89  thf('12', plain,
% 1.65/1.89      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 1.65/1.89      inference('sup+', [status(thm)], ['8', '11'])).
% 1.65/1.89  thf('13', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.89  thf('14', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.89  thf('15', plain,
% 1.65/1.89      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.65/1.89  thf('16', plain, ((r2_hidden @ sk_D @ sk_A)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('17', plain, ((r2_hidden @ sk_D @ sk_A)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf(t53_zfmisc_1, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i]:
% 1.65/1.89     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.65/1.89       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 1.65/1.89  thf('18', plain,
% 1.65/1.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.65/1.89         (~ (r2_hidden @ X13 @ X14)
% 1.65/1.89          | ~ (r2_hidden @ X15 @ X14)
% 1.65/1.89          | ((k3_xboole_0 @ (k2_tarski @ X13 @ X15) @ X14)
% 1.65/1.89              = (k2_tarski @ X13 @ X15)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 1.65/1.89  thf('19', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (((k3_xboole_0 @ (k2_tarski @ sk_D @ X0) @ sk_A)
% 1.65/1.89            = (k2_tarski @ sk_D @ X0))
% 1.65/1.89          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.65/1.89      inference('sup-', [status(thm)], ['17', '18'])).
% 1.65/1.89  thf('20', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.89  thf('21', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D @ X0))
% 1.65/1.89            = (k2_tarski @ sk_D @ X0))
% 1.65/1.89          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['19', '20'])).
% 1.65/1.89  thf('22', plain,
% 1.65/1.89      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D @ sk_D))
% 1.65/1.89         = (k2_tarski @ sk_D @ sk_D))),
% 1.65/1.89      inference('sup-', [status(thm)], ['16', '21'])).
% 1.65/1.89  thf(t69_enumset1, axiom,
% 1.65/1.89    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.65/1.89  thf('23', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.65/1.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.65/1.89  thf('24', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.65/1.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.65/1.89  thf('25', plain,
% 1.65/1.89      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 1.65/1.89      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.65/1.89  thf('26', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 1.65/1.89      inference('sup+', [status(thm)], ['15', '25'])).
% 1.65/1.89  thf('27', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf('28', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.89  thf('29', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 1.65/1.89      inference('demod', [status(thm)], ['27', '28'])).
% 1.65/1.89  thf('30', plain, ($false),
% 1.65/1.89      inference('simplify_reflect-', [status(thm)], ['26', '29'])).
% 1.65/1.89  
% 1.65/1.89  % SZS output end Refutation
% 1.65/1.89  
% 1.76/1.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
