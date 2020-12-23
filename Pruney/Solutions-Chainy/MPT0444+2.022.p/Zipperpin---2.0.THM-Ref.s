%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tn5NHNuOtJ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:48 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  244 ( 372 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tn5NHNuOtJ
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 226 iterations in 0.148s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.61  thf(commutativity_k2_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.61  thf(t12_setfam_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['0', '1'])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.61  thf(t17_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.37/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.61  thf(t25_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( v1_relat_1 @ B ) =>
% 0.37/0.61           ( ( r1_tarski @ A @ B ) =>
% 0.37/0.61             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.37/0.61               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X13)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ X14) @ (k2_relat_1 @ X13))
% 0.37/0.61          | ~ (r1_tarski @ X14 @ X13)
% 0.37/0.61          | ~ (v1_relat_1 @ X14))),
% 0.37/0.61      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.37/0.61             (k2_relat_1 @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf(fc1_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.37/0.61             (k2_relat_1 @ X0)))),
% 0.37/0.61      inference('clc', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.37/0.61           (k2_relat_1 @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['4', '9'])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.37/0.61             (k2_relat_1 @ X0)))),
% 0.37/0.61      inference('clc', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf(t19_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.37/0.61       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.61         (~ (r1_tarski @ X2 @ X3)
% 0.37/0.61          | ~ (r1_tarski @ X2 @ X4)
% 0.37/0.61          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.37/0.61             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 0.37/0.61          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.37/0.61             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 0.37/0.61          | ~ (v1_relat_1 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['10', '13'])).
% 0.37/0.61  thf(t27_relat_1, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( v1_relat_1 @ B ) =>
% 0.37/0.61           ( r1_tarski @
% 0.37/0.61             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.37/0.61             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( v1_relat_1 @ A ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( v1_relat_1 @ B ) =>
% 0.37/0.61              ( r1_tarski @
% 0.37/0.61                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.37/0.61                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.37/0.61          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('16', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('19', plain, ($false),
% 0.37/0.61      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
