%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fnq7N7zksB

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:12 EST 2020

% Result     : Timeout 58.51s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 ( 620 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( r1_tarski @ ( k5_relat_1 @ X20 @ X19 ) @ ( k5_relat_1 @ X20 @ X18 ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( r1_tarski @ ( k5_relat_1 @ X20 @ X19 ) @ ( k5_relat_1 @ X20 @ X18 ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29','30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fnq7N7zksB
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 58.51/58.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 58.51/58.71  % Solved by: fo/fo7.sh
% 58.51/58.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 58.51/58.71  % done 5353 iterations in 58.254s
% 58.51/58.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 58.51/58.71  % SZS output start Refutation
% 58.51/58.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 58.51/58.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 58.51/58.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 58.51/58.71  thf(sk_B_type, type, sk_B: $i).
% 58.51/58.71  thf(sk_A_type, type, sk_A: $i).
% 58.51/58.71  thf(sk_C_type, type, sk_C: $i).
% 58.51/58.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 58.51/58.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 58.51/58.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 58.51/58.71  thf(t48_xboole_1, axiom,
% 58.51/58.71    (![A:$i,B:$i]:
% 58.51/58.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 58.51/58.71  thf('0', plain,
% 58.51/58.71      (![X12 : $i, X13 : $i]:
% 58.51/58.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 58.51/58.71           = (k3_xboole_0 @ X12 @ X13))),
% 58.51/58.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 58.51/58.71  thf(fc2_relat_1, axiom,
% 58.51/58.71    (![A:$i,B:$i]:
% 58.51/58.71     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 58.51/58.71  thf('1', plain,
% 58.51/58.71      (![X16 : $i, X17 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k4_xboole_0 @ X16 @ X17)))),
% 58.51/58.71      inference('cnf', [status(esa)], [fc2_relat_1])).
% 58.51/58.71  thf('2', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i]:
% 58.51/58.71         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 58.51/58.71      inference('sup+', [status(thm)], ['0', '1'])).
% 58.51/58.71  thf(commutativity_k2_xboole_0, axiom,
% 58.51/58.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 58.51/58.71  thf('3', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 58.51/58.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 58.51/58.71  thf(t7_xboole_1, axiom,
% 58.51/58.71    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 58.51/58.71  thf('4', plain,
% 58.51/58.71      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 58.51/58.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 58.51/58.71  thf('5', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 58.51/58.71      inference('sup+', [status(thm)], ['3', '4'])).
% 58.51/58.71  thf(t39_xboole_1, axiom,
% 58.51/58.71    (![A:$i,B:$i]:
% 58.51/58.71     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 58.51/58.71  thf('6', plain,
% 58.51/58.71      (![X7 : $i, X8 : $i]:
% 58.51/58.71         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 58.51/58.71           = (k2_xboole_0 @ X7 @ X8))),
% 58.51/58.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 58.51/58.71  thf('7', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 58.51/58.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 58.51/58.71  thf(t43_xboole_1, axiom,
% 58.51/58.71    (![A:$i,B:$i,C:$i]:
% 58.51/58.71     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 58.51/58.71       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 58.51/58.71  thf('8', plain,
% 58.51/58.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 58.51/58.71         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 58.51/58.71          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 58.51/58.71      inference('cnf', [status(esa)], [t43_xboole_1])).
% 58.51/58.71  thf('9', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 58.51/58.71          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 58.51/58.71      inference('sup-', [status(thm)], ['7', '8'])).
% 58.51/58.71  thf('10', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 58.51/58.71          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X1))),
% 58.51/58.71      inference('sup-', [status(thm)], ['6', '9'])).
% 58.51/58.71  thf('11', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i]:
% 58.51/58.71         (r1_tarski @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X1)),
% 58.51/58.71      inference('sup-', [status(thm)], ['5', '10'])).
% 58.51/58.71  thf('12', plain,
% 58.51/58.71      (![X12 : $i, X13 : $i]:
% 58.51/58.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 58.51/58.71           = (k3_xboole_0 @ X12 @ X13))),
% 58.51/58.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 58.51/58.71  thf('13', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X1)),
% 58.51/58.71      inference('demod', [status(thm)], ['11', '12'])).
% 58.51/58.71  thf(t48_relat_1, axiom,
% 58.51/58.71    (![A:$i]:
% 58.51/58.71     ( ( v1_relat_1 @ A ) =>
% 58.51/58.71       ( ![B:$i]:
% 58.51/58.71         ( ( v1_relat_1 @ B ) =>
% 58.51/58.71           ( ![C:$i]:
% 58.51/58.71             ( ( v1_relat_1 @ C ) =>
% 58.51/58.71               ( ( r1_tarski @ A @ B ) =>
% 58.51/58.71                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 58.51/58.71  thf('14', plain,
% 58.51/58.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ X18)
% 58.51/58.71          | ~ (r1_tarski @ X19 @ X18)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X20 @ X19) @ (k5_relat_1 @ X20 @ X18))
% 58.51/58.71          | ~ (v1_relat_1 @ X20)
% 58.51/58.71          | ~ (v1_relat_1 @ X19))),
% 58.51/58.71      inference('cnf', [status(esa)], [t48_relat_1])).
% 58.51/58.71  thf('15', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 58.51/58.71          | ~ (v1_relat_1 @ X2)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.51/58.71             (k5_relat_1 @ X2 @ X0))
% 58.51/58.71          | ~ (v1_relat_1 @ X0))),
% 58.51/58.71      inference('sup-', [status(thm)], ['13', '14'])).
% 58.51/58.71  thf('16', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ X1)
% 58.51/58.71          | ~ (v1_relat_1 @ X0)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.51/58.71             (k5_relat_1 @ X2 @ X0))
% 58.51/58.71          | ~ (v1_relat_1 @ X2))),
% 58.51/58.71      inference('sup-', [status(thm)], ['2', '15'])).
% 58.51/58.71  thf('17', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i]:
% 58.51/58.71         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 58.51/58.71      inference('sup+', [status(thm)], ['0', '1'])).
% 58.51/58.71  thf(t17_xboole_1, axiom,
% 58.51/58.71    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 58.51/58.71  thf('18', plain,
% 58.51/58.71      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 58.51/58.71      inference('cnf', [status(esa)], [t17_xboole_1])).
% 58.51/58.71  thf('19', plain,
% 58.51/58.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ X18)
% 58.51/58.71          | ~ (r1_tarski @ X19 @ X18)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X20 @ X19) @ (k5_relat_1 @ X20 @ X18))
% 58.51/58.71          | ~ (v1_relat_1 @ X20)
% 58.51/58.71          | ~ (v1_relat_1 @ X19))),
% 58.51/58.71      inference('cnf', [status(esa)], [t48_relat_1])).
% 58.51/58.71  thf('20', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 58.51/58.71          | ~ (v1_relat_1 @ X2)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 58.51/58.71             (k5_relat_1 @ X2 @ X0))
% 58.51/58.71          | ~ (v1_relat_1 @ X0))),
% 58.51/58.71      inference('sup-', [status(thm)], ['18', '19'])).
% 58.51/58.71  thf('21', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ X1)
% 58.51/58.71          | ~ (v1_relat_1 @ X1)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.51/58.71             (k5_relat_1 @ X2 @ X1))
% 58.51/58.71          | ~ (v1_relat_1 @ X2))),
% 58.51/58.71      inference('sup-', [status(thm)], ['17', '20'])).
% 58.51/58.71  thf('22', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ X2)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 58.51/58.71             (k5_relat_1 @ X2 @ X1))
% 58.51/58.71          | ~ (v1_relat_1 @ X1))),
% 58.51/58.71      inference('simplify', [status(thm)], ['21'])).
% 58.51/58.71  thf(t19_xboole_1, axiom,
% 58.51/58.71    (![A:$i,B:$i,C:$i]:
% 58.51/58.71     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 58.51/58.71       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 58.51/58.71  thf('23', plain,
% 58.51/58.71      (![X4 : $i, X5 : $i, X6 : $i]:
% 58.51/58.71         (~ (r1_tarski @ X4 @ X5)
% 58.51/58.71          | ~ (r1_tarski @ X4 @ X6)
% 58.51/58.71          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 58.51/58.71      inference('cnf', [status(esa)], [t19_xboole_1])).
% 58.51/58.71  thf('24', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ X0)
% 58.51/58.71          | ~ (v1_relat_1 @ X1)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 58.51/58.71             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 58.51/58.71          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 58.51/58.71      inference('sup-', [status(thm)], ['22', '23'])).
% 58.51/58.71  thf('25', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         (~ (v1_relat_1 @ X1)
% 58.51/58.71          | ~ (v1_relat_1 @ X0)
% 58.51/58.71          | ~ (v1_relat_1 @ X2)
% 58.51/58.71          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 58.51/58.71             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 58.51/58.71          | ~ (v1_relat_1 @ X1)
% 58.51/58.71          | ~ (v1_relat_1 @ X2))),
% 58.51/58.71      inference('sup-', [status(thm)], ['16', '24'])).
% 58.51/58.71  thf('26', plain,
% 58.51/58.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.51/58.71         ((r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 58.51/58.71           (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 58.51/58.71          | ~ (v1_relat_1 @ X2)
% 58.51/58.71          | ~ (v1_relat_1 @ X0)
% 58.51/58.71          | ~ (v1_relat_1 @ X1))),
% 58.51/58.71      inference('simplify', [status(thm)], ['25'])).
% 58.51/58.71  thf(t52_relat_1, conjecture,
% 58.51/58.71    (![A:$i]:
% 58.51/58.71     ( ( v1_relat_1 @ A ) =>
% 58.51/58.71       ( ![B:$i]:
% 58.51/58.71         ( ( v1_relat_1 @ B ) =>
% 58.51/58.71           ( ![C:$i]:
% 58.51/58.71             ( ( v1_relat_1 @ C ) =>
% 58.51/58.71               ( r1_tarski @
% 58.51/58.71                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 58.51/58.71                 ( k3_xboole_0 @
% 58.51/58.71                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 58.51/58.71  thf(zf_stmt_0, negated_conjecture,
% 58.51/58.71    (~( ![A:$i]:
% 58.51/58.71        ( ( v1_relat_1 @ A ) =>
% 58.51/58.71          ( ![B:$i]:
% 58.51/58.71            ( ( v1_relat_1 @ B ) =>
% 58.51/58.71              ( ![C:$i]:
% 58.51/58.71                ( ( v1_relat_1 @ C ) =>
% 58.51/58.71                  ( r1_tarski @
% 58.51/58.71                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 58.51/58.71                    ( k3_xboole_0 @
% 58.51/58.71                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 58.51/58.71    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 58.51/58.71  thf('27', plain,
% 58.51/58.71      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 58.51/58.71          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 58.51/58.71           (k5_relat_1 @ sk_A @ sk_C)))),
% 58.51/58.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.51/58.71  thf('28', plain,
% 58.51/58.71      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 58.51/58.71      inference('sup-', [status(thm)], ['26', '27'])).
% 58.51/58.71  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 58.51/58.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.51/58.71  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 58.51/58.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.51/58.71  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 58.51/58.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.51/58.71  thf('32', plain, ($false),
% 58.51/58.71      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 58.51/58.71  
% 58.51/58.71  % SZS output end Refutation
% 58.51/58.71  
% 58.51/58.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
