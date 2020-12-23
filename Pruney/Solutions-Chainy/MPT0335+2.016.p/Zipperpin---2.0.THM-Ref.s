%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mJqoePIeZa

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:14 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X33: $i,X34: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ X33 )
        = X33 )
      | ~ ( r2_hidden @ X34 @ X33 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
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
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mJqoePIeZa
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:50:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.66/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.90  % Solved by: fo/fo7.sh
% 0.66/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.90  % done 924 iterations in 0.449s
% 0.66/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.90  % SZS output start Refutation
% 0.66/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.66/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.90  thf(t148_zfmisc_1, conjecture,
% 0.66/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.90     ( ( ( r1_tarski @ A @ B ) & 
% 0.66/0.90         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.66/0.90         ( r2_hidden @ D @ A ) ) =>
% 0.66/0.90       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.66/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.90        ( ( ( r1_tarski @ A @ B ) & 
% 0.66/0.90            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.66/0.90            ( r2_hidden @ D @ A ) ) =>
% 0.66/0.90          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.66/0.90    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.66/0.90  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf(l22_zfmisc_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( r2_hidden @ A @ B ) =>
% 0.66/0.90       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.66/0.90  thf('1', plain,
% 0.66/0.90      (![X33 : $i, X34 : $i]:
% 0.66/0.90         (((k2_xboole_0 @ (k1_tarski @ X34) @ X33) = (X33))
% 0.66/0.90          | ~ (r2_hidden @ X34 @ X33))),
% 0.66/0.90      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.66/0.90  thf('2', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 0.66/0.90      inference('sup-', [status(thm)], ['0', '1'])).
% 0.66/0.90  thf(t21_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.66/0.90  thf('3', plain,
% 0.66/0.90      (![X14 : $i, X15 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (X14))),
% 0.66/0.90      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.66/0.90  thf('4', plain,
% 0.66/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_tarski @ sk_D))),
% 0.66/0.90      inference('sup+', [status(thm)], ['2', '3'])).
% 0.66/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.90  thf('5', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('6', plain,
% 0.66/0.90      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.66/0.90      inference('demod', [status(thm)], ['4', '5'])).
% 0.66/0.90  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf(t16_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i,C:$i]:
% 0.66/0.90     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.66/0.90       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.66/0.90  thf('8', plain,
% 0.66/0.90      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.66/0.90           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.66/0.90  thf('9', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.66/0.90           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['7', '8'])).
% 0.66/0.90  thf('10', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf(t28_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.90  thf('12', plain,
% 0.66/0.90      (![X16 : $i, X17 : $i]:
% 0.66/0.90         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.66/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.90  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.66/0.90      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.90  thf('14', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['13', '14'])).
% 0.66/0.90  thf('16', plain,
% 0.66/0.90      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.66/0.90           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.66/0.90  thf('17', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ sk_A @ X0)
% 0.66/0.90           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['15', '16'])).
% 0.66/0.90  thf('18', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ sk_A @ X0)
% 0.66/0.90           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['10', '17'])).
% 0.66/0.90  thf('19', plain,
% 0.66/0.90      (((k3_xboole_0 @ sk_A @ sk_C) = (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A))),
% 0.66/0.90      inference('sup+', [status(thm)], ['9', '18'])).
% 0.66/0.90  thf('20', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('21', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('22', plain,
% 0.66/0.90      (((k3_xboole_0 @ sk_C @ sk_A) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.66/0.90      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.66/0.90  thf('23', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 0.66/0.90      inference('sup+', [status(thm)], ['6', '22'])).
% 0.66/0.90  thf('24', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('25', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('26', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.66/0.90      inference('demod', [status(thm)], ['24', '25'])).
% 0.66/0.90  thf('27', plain, ($false),
% 0.66/0.90      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 0.66/0.90  
% 0.66/0.90  % SZS output end Refutation
% 0.66/0.90  
% 0.66/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
