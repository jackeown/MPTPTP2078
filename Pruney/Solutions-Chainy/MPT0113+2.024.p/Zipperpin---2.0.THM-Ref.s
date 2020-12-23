%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xYtL52G01J

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:31 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  218 ( 326 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X28 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 )
      | ( r1_xboole_0 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['11','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xYtL52G01J
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 345 iterations in 0.119s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(t106_xboole_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.39/0.57       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.39/0.57          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf(t79_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X28 : $i, X29 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X28 @ X29) @ X29)),
% 0.39/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.39/0.57  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t63_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.57       ( r1_xboole_0 @ A @ C ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X25 @ X26)
% 0.39/0.57          | ~ (r1_xboole_0 @ X26 @ X27)
% 0.39/0.57          | (r1_xboole_0 @ X25 @ X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ sk_A @ X0)
% 0.39/0.57          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('8', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('10', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.39/0.57  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(l32_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X9 : $i, X11 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf(t52_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.39/0.57       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.39/0.57           = (k2_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ 
% 0.39/0.57              (k3_xboole_0 @ X22 @ X24)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.39/0.57  thf(t46_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X20 @ (k2_xboole_0 @ X20 @ X21)) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 0.39/0.57           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.39/0.57         = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['14', '17'])).
% 0.39/0.57  thf(t3_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('19', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('20', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('23', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.57  thf('24', plain, ($false), inference('demod', [status(thm)], ['11', '23'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
