%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ax6aKdegd3

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:54 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  260 ( 388 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t27_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ),
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
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_D ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_D ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ax6aKdegd3
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 745 iterations in 0.236s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(t27_xboole_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.46/0.68       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.46/0.68          ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t27_xboole_1])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf('2', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t12_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X5 : $i, X6 : $i]:
% 0.46/0.68         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.68  thf('4', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.68  thf(t21_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X12 : $i, X13 : $i]:
% 0.46/0.68         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.46/0.68  thf('6', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 0.46/0.68      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf(t22_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X14 : $i, X15 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf('10', plain, (((k2_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 0.46/0.68      inference('sup+', [status(thm)], ['6', '9'])).
% 0.46/0.68  thf(t17_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.46/0.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.68  thf(t10_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_D)),
% 0.46/0.68      inference('sup+', [status(thm)], ['10', '13'])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_D)),
% 0.46/0.68      inference('sup+', [status(thm)], ['1', '14'])).
% 0.46/0.68  thf('16', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X5 : $i, X6 : $i]:
% 0.46/0.68         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.68  thf('18', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X12 : $i, X13 : $i]:
% 0.46/0.68         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.46/0.68  thf('20', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf('22', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.46/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf(t19_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.46/0.68       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X9 @ X10)
% 0.46/0.68          | ~ (r1_tarski @ X9 @ X11)
% 0.46/0.68          | (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))
% 0.46/0.68          | ~ (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['15', '26'])).
% 0.46/0.68  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
