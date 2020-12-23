%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qMBqhS3diT

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  223 ( 327 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t124_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
        = ( k2_zfmisc_1 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
          = ( k2_zfmisc_1 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['7','8'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X8 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','11','12','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qMBqhS3diT
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:24:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 25 iterations in 0.020s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(t124_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.22/0.49       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.22/0.49         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.22/0.49          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.22/0.49            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.22/0.49         (k2_zfmisc_1 @ sk_B @ sk_C)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.22/0.49         (k2_zfmisc_1 @ sk_A @ sk_D)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t12_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.49  thf('5', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf(t21_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.22/0.49  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.49  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf(t123_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.22/0.49       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ (k3_xboole_0 @ X8 @ X10) @ (k3_xboole_0 @ X9 @ X11))
% 0.22/0.49           = (k3_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9) @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.49           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ X1) @ 
% 0.22/0.49              (k2_zfmisc_1 @ sk_A @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.49  thf('13', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.49  thf('15', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.22/0.49  thf('17', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 0.22/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.49  thf('19', plain, (((k3_xboole_0 @ sk_D @ sk_C) = (sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((k2_zfmisc_1 @ sk_A @ sk_C) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '11', '12', '19'])).
% 0.22/0.49  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
