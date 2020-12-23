%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ln23so2RjH

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  74 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  365 ( 536 expanded)
%              Number of equality atoms :   47 (  67 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X24: $i,X25: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ X24 )
        = X24 )
      | ~ ( r2_hidden @ X25 @ X24 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
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

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','22'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['7','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['6','33'])).

thf('35',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ln23so2RjH
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 61 iterations in 0.034s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(t148_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & 
% 0.21/0.49         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.21/0.49         ( r2_hidden @ D @ A ) ) =>
% 0.21/0.49       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ( ( r1_tarski @ A @ B ) & 
% 0.21/0.49            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.21/0.49            ( r2_hidden @ D @ A ) ) =>
% 0.21/0.49          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.21/0.49  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l22_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         (((k2_xboole_0 @ (k1_tarski @ X25) @ X24) = (X24))
% 0.21/0.49          | ~ (r2_hidden @ X25 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.21/0.49  thf('2', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t21_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_tarski @ sk_D))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l32_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X6 : $i, X8 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('10', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(t48_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.49           = (k3_xboole_0 @ X16 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('16', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.21/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X6 : $i, X8 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.49           = (k3_xboole_0 @ X16 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.49  thf('21', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.49  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '22'])).
% 0.21/0.49  thf(t16_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.49       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.21/0.49           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ sk_A @ X0)
% 0.21/0.49           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ sk_A @ X0)
% 0.21/0.49           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['7', '25'])).
% 0.21/0.49  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.21/0.49           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.21/0.49           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['26', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.49  thf('34', plain, (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '33'])).
% 0.21/0.49  thf('35', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf('37', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['34', '37'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
