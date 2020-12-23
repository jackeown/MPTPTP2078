%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oQzCxw9b2E

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:25 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 139 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  312 ( 914 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r2_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('6',plain,(
    ~ ( r2_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( r2_hidden @ X70 @ X69 )
      | ~ ( r1_tarski @ ( k2_tarski @ X68 @ X70 ) @ X69 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('13',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( r2_hidden @ X68 @ X69 )
      | ~ ( r1_tarski @ ( k2_tarski @ X68 @ X70 ) @ X69 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X68: $i,X70: $i,X71: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X68 @ X70 ) @ X71 )
      | ~ ( r2_hidden @ X70 @ X71 )
      | ~ ( r2_hidden @ X68 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r2_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','22'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('29',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( r2_hidden @ X68 @ X69 )
      | ~ ( r1_tarski @ ( k2_tarski @ X68 @ X70 ) @ X69 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('35',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oQzCxw9b2E
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 366 iterations in 0.243s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.47/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.47/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.69  thf(t47_zfmisc_1, conjecture,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.47/0.69       ( r2_hidden @ A @ C ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.69        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.47/0.69          ( r2_hidden @ A @ C ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.47/0.69  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t7_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.47/0.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.69  thf(d8_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.47/0.69       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      (![X2 : $i, X4 : $i]:
% 0.47/0.69         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.47/0.69      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.47/0.69          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.69  thf('4', plain,
% 0.47/0.69      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t60_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X9 : $i, X10 : $i]:
% 0.47/0.69         (~ (r1_tarski @ X9 @ X10) | ~ (r2_xboole_0 @ X10 @ X9))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (~ (r2_xboole_0 @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.47/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.69  thf(idempotence_k2_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.47/0.69  thf('7', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.47/0.69      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.47/0.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.69  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf(t38_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.47/0.69       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.47/0.69         ((r2_hidden @ X70 @ X69)
% 0.47/0.69          | ~ (r1_tarski @ (k2_tarski @ X68 @ X70) @ X69))),
% 0.47/0.69      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.69  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('13', plain,
% 0.47/0.69      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.47/0.69         ((r2_hidden @ X68 @ X69)
% 0.47/0.69          | ~ (r1_tarski @ (k2_tarski @ X68 @ X70) @ X69))),
% 0.47/0.69      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.69  thf('15', plain,
% 0.47/0.69      (![X68 : $i, X70 : $i, X71 : $i]:
% 0.47/0.69         ((r1_tarski @ (k2_tarski @ X68 @ X70) @ X71)
% 0.47/0.69          | ~ (r2_hidden @ X70 @ X71)
% 0.47/0.69          | ~ (r2_hidden @ X68 @ X71))),
% 0.47/0.69      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.47/0.69          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['11', '16'])).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (![X2 : $i, X4 : $i]:
% 0.47/0.69         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.47/0.69      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))
% 0.47/0.69          | (r2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.69  thf('20', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['11', '16'])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      (![X9 : $i, X10 : $i]:
% 0.47/0.69         (~ (r1_tarski @ X9 @ X10) | ~ (r2_xboole_0 @ X10 @ X9))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ~ (r2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.47/0.69      inference('clc', [status(thm)], ['19', '22'])).
% 0.47/0.69  thf(l51_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      (![X66 : $i, X67 : $i]:
% 0.47/0.69         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.47/0.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.47/0.69  thf('25', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.47/0.69  thf('26', plain,
% 0.47/0.69      (![X66 : $i, X67 : $i]:
% 0.47/0.69         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.47/0.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.47/0.69  thf('27', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.47/0.69  thf('28', plain,
% 0.47/0.69      (~ (r2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.47/0.69      inference('demod', [status(thm)], ['6', '27'])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['3', '28'])).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.47/0.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.69  thf('32', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['30', '31'])).
% 0.47/0.69  thf('33', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.47/0.69      inference('sup+', [status(thm)], ['29', '32'])).
% 0.47/0.69  thf('34', plain,
% 0.47/0.69      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.47/0.69         ((r2_hidden @ X68 @ X69)
% 0.47/0.69          | ~ (r1_tarski @ (k2_tarski @ X68 @ X70) @ X69))),
% 0.47/0.69      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.47/0.69  thf('35', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.47/0.69      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.69  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
