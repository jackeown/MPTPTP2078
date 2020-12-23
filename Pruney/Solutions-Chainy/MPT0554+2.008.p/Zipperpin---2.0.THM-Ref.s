%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GZPXGezMgu

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:30 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   56 (  61 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  292 ( 349 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( v1_xboole_0 @ X12 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ( X18 = X19 ) ) ),
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

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
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

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['14','15','20'])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X22 @ X23 ) @ ( k9_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GZPXGezMgu
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.90  % Solved by: fo/fo7.sh
% 0.68/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.90  % done 1463 iterations in 0.446s
% 0.68/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.90  % SZS output start Refutation
% 0.68/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.90  thf(t156_relat_1, conjecture,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( v1_relat_1 @ C ) =>
% 0.68/0.90       ( ( r1_tarski @ A @ B ) =>
% 0.68/0.90         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.90        ( ( v1_relat_1 @ C ) =>
% 0.68/0.90          ( ( r1_tarski @ A @ B ) =>
% 0.68/0.90            ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.68/0.90    inference('cnf.neg', [status(esa)], [t156_relat_1])).
% 0.68/0.90  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(t36_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.68/0.90  thf('1', plain,
% 0.68/0.90      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.68/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.90  thf(t1_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.68/0.90       ( r1_tarski @ A @ C ) ))).
% 0.68/0.90  thf('2', plain,
% 0.68/0.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.90         (~ (r1_tarski @ X6 @ X7)
% 0.68/0.90          | ~ (r1_tarski @ X7 @ X8)
% 0.68/0.90          | (r1_tarski @ X6 @ X8))),
% 0.68/0.90      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.68/0.90  thf('3', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.90  thf('4', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.68/0.90      inference('sup-', [status(thm)], ['0', '3'])).
% 0.68/0.90  thf(t79_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.68/0.90  thf('5', plain,
% 0.68/0.90      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.68/0.90      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.68/0.90  thf(t69_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.68/0.90       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.68/0.90  thf('6', plain,
% 0.68/0.90      (![X12 : $i, X13 : $i]:
% 0.68/0.90         (~ (r1_xboole_0 @ X12 @ X13)
% 0.68/0.90          | ~ (r1_tarski @ X12 @ X13)
% 0.68/0.90          | (v1_xboole_0 @ X12))),
% 0.68/0.90      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.68/0.90  thf('7', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.90          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.90  thf('8', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.90      inference('sup-', [status(thm)], ['4', '7'])).
% 0.68/0.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.68/0.90  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.68/0.90  thf(t8_boole, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.68/0.90  thf('10', plain,
% 0.68/0.90      (![X18 : $i, X19 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X18) | ~ (v1_xboole_0 @ X19) | ((X18) = (X19)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t8_boole])).
% 0.68/0.90  thf('11', plain,
% 0.68/0.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.90  thf('12', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.90      inference('sup-', [status(thm)], ['8', '11'])).
% 0.68/0.90  thf(t98_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.68/0.90  thf('13', plain,
% 0.68/0.90      (![X20 : $i, X21 : $i]:
% 0.68/0.90         ((k2_xboole_0 @ X20 @ X21)
% 0.68/0.90           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.68/0.90  thf('14', plain,
% 0.68/0.90      (((k2_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.68/0.90      inference('sup+', [status(thm)], ['12', '13'])).
% 0.68/0.90  thf(commutativity_k2_xboole_0, axiom,
% 0.68/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.68/0.90  thf('15', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.90  thf(t4_boole, axiom,
% 0.68/0.90    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.68/0.90  thf('16', plain,
% 0.68/0.90      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.68/0.90      inference('cnf', [status(esa)], [t4_boole])).
% 0.68/0.90  thf('17', plain,
% 0.68/0.90      (![X20 : $i, X21 : $i]:
% 0.68/0.90         ((k2_xboole_0 @ X20 @ X21)
% 0.68/0.90           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.68/0.90  thf('18', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.90      inference('sup+', [status(thm)], ['16', '17'])).
% 0.68/0.90  thf(t1_boole, axiom,
% 0.68/0.90    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.90  thf('19', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.68/0.90      inference('cnf', [status(esa)], [t1_boole])).
% 0.68/0.90  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.90      inference('sup+', [status(thm)], ['18', '19'])).
% 0.68/0.90  thf('21', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.68/0.90      inference('demod', [status(thm)], ['14', '15', '20'])).
% 0.68/0.90  thf(t153_relat_1, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( v1_relat_1 @ C ) =>
% 0.68/0.90       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.68/0.90         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.90  thf('22', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.90         (((k9_relat_1 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 0.68/0.90            = (k2_xboole_0 @ (k9_relat_1 @ X22 @ X23) @ 
% 0.68/0.90               (k9_relat_1 @ X22 @ X24)))
% 0.68/0.90          | ~ (v1_relat_1 @ X22))),
% 0.68/0.90      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.68/0.90  thf(t7_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.90  thf('23', plain,
% 0.68/0.90      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.68/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.90  thf('24', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.68/0.90           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.68/0.90          | ~ (v1_relat_1 @ X2))),
% 0.68/0.90      inference('sup+', [status(thm)], ['22', '23'])).
% 0.68/0.90  thf('25', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.68/0.90          | ~ (v1_relat_1 @ X0))),
% 0.68/0.90      inference('sup+', [status(thm)], ['21', '24'])).
% 0.68/0.90  thf('26', plain,
% 0.68/0.90      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('27', plain, (~ (v1_relat_1 @ sk_C)),
% 0.68/0.90      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.90  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 0.68/0.90  
% 0.68/0.90  % SZS output end Refutation
% 0.68/0.90  
% 0.68/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
