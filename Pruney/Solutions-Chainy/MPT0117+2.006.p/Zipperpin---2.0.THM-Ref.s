%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Apb12Ok29y

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:47 EST 2020

% Result     : Theorem 17.03s
% Output     : Refutation 17.03s
% Verified   : 
% Statistics : Number of formulae       :   44 (  48 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  278 ( 322 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ( r1_tarski @ ( k2_xboole_0 @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ( r1_tarski @ ( k2_xboole_0 @ X31 @ X33 ) @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Apb12Ok29y
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.03/17.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 17.03/17.24  % Solved by: fo/fo7.sh
% 17.03/17.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.03/17.24  % done 21648 iterations in 16.791s
% 17.03/17.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 17.03/17.24  % SZS output start Refutation
% 17.03/17.24  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 17.03/17.24  thf(sk_A_type, type, sk_A: $i).
% 17.03/17.24  thf(sk_C_type, type, sk_C: $i).
% 17.03/17.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.03/17.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.03/17.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.03/17.24  thf(sk_B_type, type, sk_B: $i).
% 17.03/17.24  thf(t110_xboole_1, conjecture,
% 17.03/17.24    (![A:$i,B:$i,C:$i]:
% 17.03/17.24     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.03/17.24       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 17.03/17.24  thf(zf_stmt_0, negated_conjecture,
% 17.03/17.24    (~( ![A:$i,B:$i,C:$i]:
% 17.03/17.24        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.03/17.24          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 17.03/17.24    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 17.03/17.24  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 17.03/17.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.03/17.24  thf(commutativity_k2_xboole_0, axiom,
% 17.03/17.24    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 17.03/17.24  thf('1', plain,
% 17.03/17.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 17.03/17.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 17.03/17.24  thf(t7_xboole_1, axiom,
% 17.03/17.24    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 17.03/17.24  thf('2', plain,
% 17.03/17.24      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 17.03/17.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 17.03/17.24  thf('3', plain, ((r1_tarski @ sk_C @ sk_B)),
% 17.03/17.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.03/17.24  thf(t12_xboole_1, axiom,
% 17.03/17.24    (![A:$i,B:$i]:
% 17.03/17.24     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 17.03/17.24  thf('4', plain,
% 17.03/17.24      (![X12 : $i, X13 : $i]:
% 17.03/17.24         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 17.03/17.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 17.03/17.24  thf('5', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 17.03/17.25      inference('sup-', [status(thm)], ['3', '4'])).
% 17.03/17.25  thf(t11_xboole_1, axiom,
% 17.03/17.25    (![A:$i,B:$i,C:$i]:
% 17.03/17.25     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 17.03/17.25  thf('6', plain,
% 17.03/17.25      (![X9 : $i, X10 : $i, X11 : $i]:
% 17.03/17.25         ((r1_tarski @ X9 @ X10)
% 17.03/17.25          | ~ (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 17.03/17.25      inference('cnf', [status(esa)], [t11_xboole_1])).
% 17.03/17.25  thf('7', plain,
% 17.03/17.25      (![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_C @ X0))),
% 17.03/17.25      inference('sup-', [status(thm)], ['5', '6'])).
% 17.03/17.25  thf('8', plain, (![X0 : $i]: (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ X0))),
% 17.03/17.25      inference('sup-', [status(thm)], ['2', '7'])).
% 17.03/17.25  thf('9', plain, (![X0 : $i]: (r1_tarski @ sk_C @ (k2_xboole_0 @ X0 @ sk_B))),
% 17.03/17.25      inference('sup+', [status(thm)], ['1', '8'])).
% 17.03/17.25  thf(t43_xboole_1, axiom,
% 17.03/17.25    (![A:$i,B:$i,C:$i]:
% 17.03/17.25     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 17.03/17.25       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 17.03/17.25  thf('10', plain,
% 17.03/17.25      (![X19 : $i, X20 : $i, X21 : $i]:
% 17.03/17.25         ((r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 17.03/17.25          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 17.03/17.25      inference('cnf', [status(esa)], [t43_xboole_1])).
% 17.03/17.25  thf('11', plain,
% 17.03/17.25      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_B)),
% 17.03/17.25      inference('sup-', [status(thm)], ['9', '10'])).
% 17.03/17.25  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 17.03/17.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.03/17.25  thf(t8_xboole_1, axiom,
% 17.03/17.25    (![A:$i,B:$i,C:$i]:
% 17.03/17.25     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.03/17.25       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 17.03/17.25  thf('13', plain,
% 17.03/17.25      (![X28 : $i, X29 : $i, X30 : $i]:
% 17.03/17.25         (~ (r1_tarski @ X28 @ X29)
% 17.03/17.25          | ~ (r1_tarski @ X30 @ X29)
% 17.03/17.25          | (r1_tarski @ (k2_xboole_0 @ X28 @ X30) @ X29))),
% 17.03/17.25      inference('cnf', [status(esa)], [t8_xboole_1])).
% 17.03/17.25  thf('14', plain,
% 17.03/17.25      (![X0 : $i]:
% 17.03/17.25         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 17.03/17.25          | ~ (r1_tarski @ X0 @ sk_B))),
% 17.03/17.25      inference('sup-', [status(thm)], ['12', '13'])).
% 17.03/17.25  thf('15', plain,
% 17.03/17.25      (![X0 : $i]:
% 17.03/17.25         (r1_tarski @ (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0)) @ sk_B)),
% 17.03/17.25      inference('sup-', [status(thm)], ['11', '14'])).
% 17.03/17.25  thf(d6_xboole_0, axiom,
% 17.03/17.25    (![A:$i,B:$i]:
% 17.03/17.25     ( ( k5_xboole_0 @ A @ B ) =
% 17.03/17.25       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 17.03/17.25  thf('16', plain,
% 17.03/17.25      (![X2 : $i, X3 : $i]:
% 17.03/17.25         ((k5_xboole_0 @ X2 @ X3)
% 17.03/17.25           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 17.03/17.25      inference('cnf', [status(esa)], [d6_xboole_0])).
% 17.03/17.25  thf(t36_xboole_1, axiom,
% 17.03/17.25    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 17.03/17.25  thf('17', plain,
% 17.03/17.25      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 17.03/17.25      inference('cnf', [status(esa)], [t36_xboole_1])).
% 17.03/17.25  thf(t9_xboole_1, axiom,
% 17.03/17.25    (![A:$i,B:$i,C:$i]:
% 17.03/17.25     ( ( r1_tarski @ A @ B ) =>
% 17.03/17.25       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 17.03/17.25  thf('18', plain,
% 17.03/17.25      (![X31 : $i, X32 : $i, X33 : $i]:
% 17.03/17.25         (~ (r1_tarski @ X31 @ X32)
% 17.03/17.25          | (r1_tarski @ (k2_xboole_0 @ X31 @ X33) @ (k2_xboole_0 @ X32 @ X33)))),
% 17.03/17.25      inference('cnf', [status(esa)], [t9_xboole_1])).
% 17.03/17.25  thf('19', plain,
% 17.03/17.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.03/17.25         (r1_tarski @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ 
% 17.03/17.25          (k2_xboole_0 @ X0 @ X2))),
% 17.03/17.25      inference('sup-', [status(thm)], ['17', '18'])).
% 17.03/17.25  thf('20', plain,
% 17.03/17.25      (![X0 : $i, X1 : $i]:
% 17.03/17.25         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ 
% 17.03/17.25          (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 17.03/17.25      inference('sup+', [status(thm)], ['16', '19'])).
% 17.03/17.25  thf(t1_xboole_1, axiom,
% 17.03/17.25    (![A:$i,B:$i,C:$i]:
% 17.03/17.25     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 17.03/17.25       ( r1_tarski @ A @ C ) ))).
% 17.03/17.25  thf('21', plain,
% 17.03/17.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.03/17.25         (~ (r1_tarski @ X14 @ X15)
% 17.03/17.25          | ~ (r1_tarski @ X15 @ X16)
% 17.03/17.25          | (r1_tarski @ X14 @ X16))),
% 17.03/17.25      inference('cnf', [status(esa)], [t1_xboole_1])).
% 17.03/17.25  thf('22', plain,
% 17.03/17.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.03/17.25         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X2)
% 17.03/17.25          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 17.03/17.25      inference('sup-', [status(thm)], ['20', '21'])).
% 17.03/17.25  thf('23', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 17.03/17.25      inference('sup-', [status(thm)], ['15', '22'])).
% 17.03/17.25  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 17.03/17.25  
% 17.03/17.25  % SZS output end Refutation
% 17.03/17.25  
% 17.03/17.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
