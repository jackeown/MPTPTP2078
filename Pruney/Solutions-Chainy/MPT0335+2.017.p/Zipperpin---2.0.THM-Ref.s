%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LLLIbrtOPG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:14 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  271 ( 425 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X31 ) @ X30 )
        = X30 )
      | ~ ( r2_hidden @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['6','22'])).

thf('24',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LLLIbrtOPG
% 0.13/0.37  % Computer   : n006.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:11:23 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 551 iterations in 0.248s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(t148_zfmisc_1, conjecture,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( ( r1_tarski @ A @ B ) & 
% 0.53/0.74         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.53/0.74         ( r2_hidden @ D @ A ) ) =>
% 0.53/0.74       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74        ( ( ( r1_tarski @ A @ B ) & 
% 0.53/0.74            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.53/0.74            ( r2_hidden @ D @ A ) ) =>
% 0.53/0.74          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.53/0.74  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(l22_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( r2_hidden @ A @ B ) =>
% 0.53/0.74       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (![X30 : $i, X31 : $i]:
% 0.53/0.74         (((k2_xboole_0 @ (k1_tarski @ X31) @ X30) = (X30))
% 0.53/0.74          | ~ (r2_hidden @ X31 @ X30))),
% 0.53/0.74      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.53/0.74  thf('2', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.74  thf(t21_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (![X10 : $i, X11 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (X10))),
% 0.53/0.74      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_tarski @ sk_D))),
% 0.53/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.53/0.74  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.53/0.74      inference('demod', [status(thm)], ['4', '5'])).
% 0.53/0.74  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t16_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.74       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.53/0.74           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.53/0.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['7', '8'])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.74  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t28_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i]:
% 0.53/0.74         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.74  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.74  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '14'])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.53/0.74           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ sk_A @ X0)
% 0.53/0.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['15', '16'])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ sk_A @ X0)
% 0.53/0.74           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '17'])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      (((k3_xboole_0 @ sk_A @ sk_C) = (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A))),
% 0.53/0.74      inference('sup+', [status(thm)], ['9', '18'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (((k3_xboole_0 @ sk_C @ sk_A) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.53/0.74      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.53/0.74  thf('23', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 0.53/0.74      inference('sup+', [status(thm)], ['6', '22'])).
% 0.53/0.74  thf('24', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.74  thf('26', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.53/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.53/0.74  thf('27', plain, ($false),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
