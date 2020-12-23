%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c4nRBUmukG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:13 EST 2020

% Result     : Theorem 44.51s
% Output     : Refutation 44.51s
% Verified   : 
% Statistics : Number of formulae       :   44 (  53 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  395 ( 538 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ( r1_tarski @ ( k5_relat_1 @ X19 @ X18 ) @ ( k5_relat_1 @ X19 @ X17 ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ( r1_tarski @ ( k5_relat_1 @ X19 @ X18 ) @ ( k5_relat_1 @ X19 @ X17 ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

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

thf('21',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c4nRBUmukG
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:43:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 44.51/44.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 44.51/44.69  % Solved by: fo/fo7.sh
% 44.51/44.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.51/44.69  % done 2659 iterations in 44.231s
% 44.51/44.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 44.51/44.69  % SZS output start Refutation
% 44.51/44.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 44.51/44.69  thf(sk_B_type, type, sk_B: $i).
% 44.51/44.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.51/44.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 44.51/44.69  thf(sk_C_type, type, sk_C: $i).
% 44.51/44.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 44.51/44.69  thf(sk_A_type, type, sk_A: $i).
% 44.51/44.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 44.51/44.69  thf(fc1_relat_1, axiom,
% 44.51/44.69    (![A:$i,B:$i]:
% 44.51/44.69     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 44.51/44.69  thf('0', plain,
% 44.51/44.69      (![X15 : $i, X16 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k3_xboole_0 @ X15 @ X16)))),
% 44.51/44.69      inference('cnf', [status(esa)], [fc1_relat_1])).
% 44.51/44.69  thf(t22_xboole_1, axiom,
% 44.51/44.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 44.51/44.69  thf('1', plain,
% 44.51/44.69      (![X5 : $i, X6 : $i]:
% 44.51/44.69         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 44.51/44.69      inference('cnf', [status(esa)], [t22_xboole_1])).
% 44.51/44.69  thf(t31_xboole_1, axiom,
% 44.51/44.69    (![A:$i,B:$i,C:$i]:
% 44.51/44.69     ( r1_tarski @
% 44.51/44.69       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 44.51/44.69       ( k2_xboole_0 @ B @ C ) ))).
% 44.51/44.69  thf('2', plain,
% 44.51/44.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 44.51/44.69         (r1_tarski @ 
% 44.51/44.69          (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k3_xboole_0 @ X10 @ X12)) @ 
% 44.51/44.69          (k2_xboole_0 @ X11 @ X12))),
% 44.51/44.69      inference('cnf', [status(esa)], [t31_xboole_1])).
% 44.51/44.69  thf(t23_xboole_1, axiom,
% 44.51/44.69    (![A:$i,B:$i,C:$i]:
% 44.51/44.69     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 44.51/44.69       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 44.51/44.69  thf('3', plain,
% 44.51/44.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 44.51/44.69         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 44.51/44.69           = (k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 44.51/44.69      inference('cnf', [status(esa)], [t23_xboole_1])).
% 44.51/44.69  thf('4', plain,
% 44.51/44.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 44.51/44.69         (r1_tarski @ (k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)) @ 
% 44.51/44.69          (k2_xboole_0 @ X11 @ X12))),
% 44.51/44.69      inference('demod', [status(thm)], ['2', '3'])).
% 44.51/44.69  thf('5', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.51/44.69         (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 44.51/44.69          (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 44.51/44.69      inference('sup+', [status(thm)], ['1', '4'])).
% 44.51/44.69  thf('6', plain,
% 44.51/44.69      (![X5 : $i, X6 : $i]:
% 44.51/44.69         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 44.51/44.69      inference('cnf', [status(esa)], [t22_xboole_1])).
% 44.51/44.69  thf('7', plain,
% 44.51/44.69      (![X0 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X0)),
% 44.51/44.69      inference('demod', [status(thm)], ['5', '6'])).
% 44.51/44.69  thf(t48_relat_1, axiom,
% 44.51/44.69    (![A:$i]:
% 44.51/44.69     ( ( v1_relat_1 @ A ) =>
% 44.51/44.69       ( ![B:$i]:
% 44.51/44.69         ( ( v1_relat_1 @ B ) =>
% 44.51/44.69           ( ![C:$i]:
% 44.51/44.69             ( ( v1_relat_1 @ C ) =>
% 44.51/44.69               ( ( r1_tarski @ A @ B ) =>
% 44.51/44.69                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 44.51/44.69  thf('8', plain,
% 44.51/44.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X17)
% 44.51/44.69          | ~ (r1_tarski @ X18 @ X17)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X19 @ X18) @ (k5_relat_1 @ X19 @ X17))
% 44.51/44.69          | ~ (v1_relat_1 @ X19)
% 44.51/44.69          | ~ (v1_relat_1 @ X18))),
% 44.51/44.69      inference('cnf', [status(esa)], [t48_relat_1])).
% 44.51/44.69  thf('9', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 44.51/44.69          | ~ (v1_relat_1 @ X2)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 44.51/44.69             (k5_relat_1 @ X2 @ X0))
% 44.51/44.69          | ~ (v1_relat_1 @ X0))),
% 44.51/44.69      inference('sup-', [status(thm)], ['7', '8'])).
% 44.51/44.69  thf('10', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X1)
% 44.51/44.69          | ~ (v1_relat_1 @ X0)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 44.51/44.69             (k5_relat_1 @ X2 @ X0))
% 44.51/44.69          | ~ (v1_relat_1 @ X2))),
% 44.51/44.69      inference('sup-', [status(thm)], ['0', '9'])).
% 44.51/44.69  thf('11', plain,
% 44.51/44.69      (![X15 : $i, X16 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k3_xboole_0 @ X15 @ X16)))),
% 44.51/44.69      inference('cnf', [status(esa)], [fc1_relat_1])).
% 44.51/44.69  thf(t17_xboole_1, axiom,
% 44.51/44.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 44.51/44.69  thf('12', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 44.51/44.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 44.51/44.69  thf('13', plain,
% 44.51/44.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X17)
% 44.51/44.69          | ~ (r1_tarski @ X18 @ X17)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X19 @ X18) @ (k5_relat_1 @ X19 @ X17))
% 44.51/44.69          | ~ (v1_relat_1 @ X19)
% 44.51/44.69          | ~ (v1_relat_1 @ X18))),
% 44.51/44.69      inference('cnf', [status(esa)], [t48_relat_1])).
% 44.51/44.69  thf('14', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 44.51/44.69          | ~ (v1_relat_1 @ X2)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 44.51/44.69             (k5_relat_1 @ X2 @ X0))
% 44.51/44.69          | ~ (v1_relat_1 @ X0))),
% 44.51/44.69      inference('sup-', [status(thm)], ['12', '13'])).
% 44.51/44.69  thf('15', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X1)
% 44.51/44.69          | ~ (v1_relat_1 @ X1)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 44.51/44.69             (k5_relat_1 @ X2 @ X1))
% 44.51/44.69          | ~ (v1_relat_1 @ X2))),
% 44.51/44.69      inference('sup-', [status(thm)], ['11', '14'])).
% 44.51/44.69  thf('16', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X2)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 44.51/44.69             (k5_relat_1 @ X2 @ X1))
% 44.51/44.69          | ~ (v1_relat_1 @ X1))),
% 44.51/44.69      inference('simplify', [status(thm)], ['15'])).
% 44.51/44.69  thf(t19_xboole_1, axiom,
% 44.51/44.69    (![A:$i,B:$i,C:$i]:
% 44.51/44.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 44.51/44.69       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 44.51/44.69  thf('17', plain,
% 44.51/44.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 44.51/44.69         (~ (r1_tarski @ X2 @ X3)
% 44.51/44.69          | ~ (r1_tarski @ X2 @ X4)
% 44.51/44.69          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 44.51/44.69      inference('cnf', [status(esa)], [t19_xboole_1])).
% 44.51/44.69  thf('18', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X0)
% 44.51/44.69          | ~ (v1_relat_1 @ X1)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 44.51/44.69             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 44.51/44.69          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 44.51/44.69      inference('sup-', [status(thm)], ['16', '17'])).
% 44.51/44.69  thf('19', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.51/44.69         (~ (v1_relat_1 @ X1)
% 44.51/44.69          | ~ (v1_relat_1 @ X0)
% 44.51/44.69          | ~ (v1_relat_1 @ X2)
% 44.51/44.69          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 44.51/44.69             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 44.51/44.69          | ~ (v1_relat_1 @ X1)
% 44.51/44.69          | ~ (v1_relat_1 @ X2))),
% 44.51/44.69      inference('sup-', [status(thm)], ['10', '18'])).
% 44.51/44.69  thf('20', plain,
% 44.51/44.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.51/44.69         ((r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 44.51/44.69           (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 44.51/44.69          | ~ (v1_relat_1 @ X2)
% 44.51/44.69          | ~ (v1_relat_1 @ X0)
% 44.51/44.69          | ~ (v1_relat_1 @ X1))),
% 44.51/44.69      inference('simplify', [status(thm)], ['19'])).
% 44.51/44.69  thf(t52_relat_1, conjecture,
% 44.51/44.69    (![A:$i]:
% 44.51/44.69     ( ( v1_relat_1 @ A ) =>
% 44.51/44.69       ( ![B:$i]:
% 44.51/44.69         ( ( v1_relat_1 @ B ) =>
% 44.51/44.69           ( ![C:$i]:
% 44.51/44.69             ( ( v1_relat_1 @ C ) =>
% 44.51/44.69               ( r1_tarski @
% 44.51/44.69                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 44.51/44.69                 ( k3_xboole_0 @
% 44.51/44.69                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 44.51/44.69  thf(zf_stmt_0, negated_conjecture,
% 44.51/44.69    (~( ![A:$i]:
% 44.51/44.69        ( ( v1_relat_1 @ A ) =>
% 44.51/44.69          ( ![B:$i]:
% 44.51/44.69            ( ( v1_relat_1 @ B ) =>
% 44.51/44.69              ( ![C:$i]:
% 44.51/44.69                ( ( v1_relat_1 @ C ) =>
% 44.51/44.69                  ( r1_tarski @
% 44.51/44.69                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 44.51/44.69                    ( k3_xboole_0 @
% 44.51/44.69                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 44.51/44.69    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 44.51/44.69  thf('21', plain,
% 44.51/44.69      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 44.51/44.69          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 44.51/44.69           (k5_relat_1 @ sk_A @ sk_C)))),
% 44.51/44.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.51/44.69  thf('22', plain,
% 44.51/44.69      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 44.51/44.69      inference('sup-', [status(thm)], ['20', '21'])).
% 44.51/44.69  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 44.51/44.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.51/44.69  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 44.51/44.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.51/44.69  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 44.51/44.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.51/44.69  thf('26', plain, ($false),
% 44.51/44.69      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 44.51/44.69  
% 44.51/44.69  % SZS output end Refutation
% 44.51/44.69  
% 44.51/44.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
