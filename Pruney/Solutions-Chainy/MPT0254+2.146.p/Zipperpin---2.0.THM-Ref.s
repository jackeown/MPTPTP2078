%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1sCNgxxEvQ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:54 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  237 ( 324 expanded)
%              Number of equality atoms :   38 (  57 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','11'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['15'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('17',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46 != X45 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X45 ) )
       != ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('18',plain,(
    ! [X45: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X45 ) @ ( k1_tarski @ X45 ) )
     != ( k1_tarski @ X45 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['15'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['15'])).

thf('22',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1sCNgxxEvQ
% 0.14/0.37  % Computer   : n015.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:44:53 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 46 iterations in 0.023s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(t5_boole, axiom,
% 0.23/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.50  thf('0', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.23/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.23/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.23/0.50  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.23/0.50  thf(t95_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k3_xboole_0 @ A @ B ) =
% 0.23/0.50       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i]:
% 0.23/0.50         ((k3_xboole_0 @ X10 @ X11)
% 0.23/0.50           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.23/0.50              (k2_xboole_0 @ X10 @ X11)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.23/0.50  thf(t91_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.23/0.50       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.23/0.50           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i]:
% 0.23/0.50         ((k3_xboole_0 @ X10 @ X11)
% 0.23/0.50           = (k5_xboole_0 @ X10 @ 
% 0.23/0.50              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 0.23/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((k3_xboole_0 @ X0 @ X0)
% 0.23/0.50           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.23/0.50      inference('sup+', [status(thm)], ['1', '4'])).
% 0.23/0.50  thf(t92_xboole_1, axiom,
% 0.23/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.50  thf('6', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf('8', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.23/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.23/0.50  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf(t100_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X1 : $i, X2 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.23/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['0', '11'])).
% 0.23/0.50  thf(t49_zfmisc_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t15_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.23/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         (((X3) = (k1_xboole_0)) | ((k2_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.50  thf('16', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.50  thf(t20_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.23/0.50         ( k1_tarski @ A ) ) <=>
% 0.23/0.50       ( ( A ) != ( B ) ) ))).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X45 : $i, X46 : $i]:
% 0.23/0.50         (((X46) != (X45))
% 0.23/0.50          | ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X45))
% 0.23/0.50              != (k1_tarski @ X46)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X45 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ (k1_tarski @ X45) @ (k1_tarski @ X45))
% 0.23/0.50           != (k1_tarski @ X45))),
% 0.23/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['16', '18'])).
% 0.23/0.50  thf('20', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.50  thf('21', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.50  thf('22', plain,
% 0.23/0.50      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.23/0.50  thf('23', plain, ($false),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['12', '22'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
