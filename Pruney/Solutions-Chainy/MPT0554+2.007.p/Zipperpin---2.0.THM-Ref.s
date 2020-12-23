%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2bmsNQd5rr

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:30 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  280 ( 342 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t156_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ( X19 = X20 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','18','19'])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_relat_1 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X21 @ X22 ) @ ( k9_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2bmsNQd5rr
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 1372 iterations in 0.367s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.81  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.61/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.81  thf(t156_relat_1, conjecture,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( v1_relat_1 @ C ) =>
% 0.61/0.81       ( ( r1_tarski @ A @ B ) =>
% 0.61/0.81         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.81        ( ( v1_relat_1 @ C ) =>
% 0.61/0.81          ( ( r1_tarski @ A @ B ) =>
% 0.61/0.81            ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t156_relat_1])).
% 0.61/0.81  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t36_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.81  thf('1', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.61/0.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.81  thf(t1_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.61/0.81       ( r1_tarski @ A @ C ) ))).
% 0.61/0.81  thf('2', plain,
% 0.61/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.61/0.81         (~ (r1_tarski @ X6 @ X7)
% 0.61/0.81          | ~ (r1_tarski @ X7 @ X8)
% 0.61/0.81          | (r1_tarski @ X6 @ X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.61/0.81  thf('3', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.61/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.82  thf('4', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.61/0.82      inference('sup-', [status(thm)], ['0', '3'])).
% 0.61/0.82  thf(t79_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.61/0.82  thf('5', plain,
% 0.61/0.82      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.61/0.82      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.61/0.82  thf(t69_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.61/0.82       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.61/0.82  thf('6', plain,
% 0.61/0.82      (![X13 : $i, X14 : $i]:
% 0.61/0.82         (~ (r1_xboole_0 @ X13 @ X14)
% 0.61/0.82          | ~ (r1_tarski @ X13 @ X14)
% 0.61/0.82          | (v1_xboole_0 @ X13))),
% 0.61/0.82      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.61/0.82  thf('7', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.61/0.82          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.82  thf('8', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['4', '7'])).
% 0.61/0.82  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.61/0.82  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.61/0.82  thf(t8_boole, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.61/0.82  thf('10', plain,
% 0.61/0.82      (![X19 : $i, X20 : $i]:
% 0.61/0.82         (~ (v1_xboole_0 @ X19) | ~ (v1_xboole_0 @ X20) | ((X19) = (X20)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t8_boole])).
% 0.61/0.82  thf('11', plain,
% 0.61/0.82      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.82  thf('12', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['8', '11'])).
% 0.61/0.82  thf(t39_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.82  thf('13', plain,
% 0.61/0.82      (![X11 : $i, X12 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.61/0.82           = (k2_xboole_0 @ X11 @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.82  thf('14', plain,
% 0.61/0.82      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.61/0.82      inference('sup+', [status(thm)], ['12', '13'])).
% 0.61/0.82  thf(commutativity_k2_xboole_0, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.61/0.82  thf('15', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.82  thf('16', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.82  thf(t1_boole, axiom,
% 0.61/0.82    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.82  thf('17', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.61/0.82      inference('cnf', [status(esa)], [t1_boole])).
% 0.61/0.82  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['16', '17'])).
% 0.61/0.82  thf('19', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.82  thf('20', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['14', '15', '18', '19'])).
% 0.61/0.82  thf(t153_relat_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( v1_relat_1 @ C ) =>
% 0.61/0.82       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.61/0.82         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.61/0.82  thf('21', plain,
% 0.61/0.82      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.61/0.82         (((k9_relat_1 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.61/0.82            = (k2_xboole_0 @ (k9_relat_1 @ X21 @ X22) @ 
% 0.61/0.82               (k9_relat_1 @ X21 @ X23)))
% 0.61/0.82          | ~ (v1_relat_1 @ X21))),
% 0.61/0.82      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.61/0.82  thf(t7_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.82  thf('22', plain,
% 0.61/0.82      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.61/0.82      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.61/0.82  thf('23', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.82         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.61/0.82           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.61/0.82          | ~ (v1_relat_1 @ X2))),
% 0.61/0.82      inference('sup+', [status(thm)], ['21', '22'])).
% 0.61/0.82  thf('24', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.61/0.82          | ~ (v1_relat_1 @ X0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['20', '23'])).
% 0.61/0.82  thf('25', plain,
% 0.61/0.82      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('26', plain, (~ (v1_relat_1 @ sk_C)),
% 0.61/0.82      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.82  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('28', plain, ($false), inference('demod', [status(thm)], ['26', '27'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
