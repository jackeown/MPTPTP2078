%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NB4v7XuJbe

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  237 ( 345 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['11','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NB4v7XuJbe
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 10:10:49 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 88 iterations in 0.034s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.52  thf(t106_xboole_1, conjecture,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.23/0.52       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.52        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.23/0.52          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf(t79_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.23/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.23/0.52  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(t63_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.23/0.52       ( r1_xboole_0 @ A @ C ) ))).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.52         (~ (r1_tarski @ X17 @ X18)
% 0.23/0.52          | ~ (r1_xboole_0 @ X18 @ X19)
% 0.23/0.52          | (r1_xboole_0 @ X17 @ X19))),
% 0.23/0.52      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r1_xboole_0 @ sk_A @ X0)
% 0.23/0.52          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.52  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.23/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('8', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.23/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('10', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.23/0.52      inference('sat_resolution*', [status(thm)], ['8', '9'])).
% 0.23/0.52  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.23/0.52      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.23/0.52  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(t28_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      (![X8 : $i, X9 : $i]:
% 0.23/0.52         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.23/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.52  thf(t49_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.23/0.52       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.52         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.23/0.52           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.23/0.52      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C) = (sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.23/0.52  thf(t36_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.23/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.23/0.52  thf(l32_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X0 : $i, X2 : $i]:
% 0.23/0.52         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.23/0.52      inference('sup+', [status(thm)], ['16', '19'])).
% 0.23/0.52  thf(t47_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (![X12 : $i, X13 : $i]:
% 0.23/0.52         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.23/0.52           = (k4_xboole_0 @ X12 @ X13))),
% 0.23/0.52      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.23/0.52  thf('22', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.23/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.23/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.52  thf('24', plain,
% 0.23/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.52  thf('25', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.23/0.52  thf('26', plain, ($false), inference('demod', [status(thm)], ['11', '25'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
