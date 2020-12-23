%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g0Y6i1IvgU

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:12 EST 2020

% Result     : Theorem 32.85s
% Output     : Refutation 32.85s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  287 ( 487 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k5_relat_1 @ X11 @ X10 ) @ ( k5_relat_1 @ X11 @ X9 ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15','16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g0Y6i1IvgU
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:04:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 32.85/33.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 32.85/33.05  % Solved by: fo/fo7.sh
% 32.85/33.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.85/33.05  % done 8584 iterations in 32.603s
% 32.85/33.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 32.85/33.05  % SZS output start Refutation
% 32.85/33.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.85/33.05  thf(sk_A_type, type, sk_A: $i).
% 32.85/33.05  thf(sk_B_type, type, sk_B: $i).
% 32.85/33.05  thf(sk_C_type, type, sk_C: $i).
% 32.85/33.05  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 32.85/33.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 32.85/33.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.85/33.05  thf(commutativity_k3_xboole_0, axiom,
% 32.85/33.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 32.85/33.05  thf('0', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 32.85/33.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 32.85/33.05  thf(fc1_relat_1, axiom,
% 32.85/33.05    (![A:$i,B:$i]:
% 32.85/33.05     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 32.85/33.05  thf('1', plain,
% 32.85/33.05      (![X7 : $i, X8 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k3_xboole_0 @ X7 @ X8)))),
% 32.85/33.05      inference('cnf', [status(esa)], [fc1_relat_1])).
% 32.85/33.05  thf(t17_xboole_1, axiom,
% 32.85/33.05    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 32.85/33.05  thf('2', plain,
% 32.85/33.05      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 32.85/33.05      inference('cnf', [status(esa)], [t17_xboole_1])).
% 32.85/33.05  thf(t48_relat_1, axiom,
% 32.85/33.05    (![A:$i]:
% 32.85/33.05     ( ( v1_relat_1 @ A ) =>
% 32.85/33.05       ( ![B:$i]:
% 32.85/33.05         ( ( v1_relat_1 @ B ) =>
% 32.85/33.05           ( ![C:$i]:
% 32.85/33.05             ( ( v1_relat_1 @ C ) =>
% 32.85/33.05               ( ( r1_tarski @ A @ B ) =>
% 32.85/33.05                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 32.85/33.05  thf('3', plain,
% 32.85/33.05      (![X9 : $i, X10 : $i, X11 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ X9)
% 32.85/33.05          | ~ (r1_tarski @ X10 @ X9)
% 32.85/33.05          | (r1_tarski @ (k5_relat_1 @ X11 @ X10) @ (k5_relat_1 @ X11 @ X9))
% 32.85/33.05          | ~ (v1_relat_1 @ X11)
% 32.85/33.05          | ~ (v1_relat_1 @ X10))),
% 32.85/33.05      inference('cnf', [status(esa)], [t48_relat_1])).
% 32.85/33.05  thf('4', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 32.85/33.05          | ~ (v1_relat_1 @ X2)
% 32.85/33.05          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 32.85/33.05             (k5_relat_1 @ X2 @ X0))
% 32.85/33.05          | ~ (v1_relat_1 @ X0))),
% 32.85/33.05      inference('sup-', [status(thm)], ['2', '3'])).
% 32.85/33.05  thf('5', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ X1)
% 32.85/33.05          | ~ (v1_relat_1 @ X1)
% 32.85/33.05          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 32.85/33.05             (k5_relat_1 @ X2 @ X1))
% 32.85/33.05          | ~ (v1_relat_1 @ X2))),
% 32.85/33.05      inference('sup-', [status(thm)], ['1', '4'])).
% 32.85/33.05  thf('6', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ X2)
% 32.85/33.05          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 32.85/33.05             (k5_relat_1 @ X2 @ X1))
% 32.85/33.05          | ~ (v1_relat_1 @ X1))),
% 32.85/33.05      inference('simplify', [status(thm)], ['5'])).
% 32.85/33.05  thf('7', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.85/33.05         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 32.85/33.05           (k5_relat_1 @ X2 @ X0))
% 32.85/33.05          | ~ (v1_relat_1 @ X0)
% 32.85/33.05          | ~ (v1_relat_1 @ X2))),
% 32.85/33.05      inference('sup+', [status(thm)], ['0', '6'])).
% 32.85/33.05  thf('8', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ X2)
% 32.85/33.05          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 32.85/33.05             (k5_relat_1 @ X2 @ X1))
% 32.85/33.05          | ~ (v1_relat_1 @ X1))),
% 32.85/33.05      inference('simplify', [status(thm)], ['5'])).
% 32.85/33.05  thf(t19_xboole_1, axiom,
% 32.85/33.05    (![A:$i,B:$i,C:$i]:
% 32.85/33.05     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 32.85/33.05       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 32.85/33.05  thf('9', plain,
% 32.85/33.05      (![X4 : $i, X5 : $i, X6 : $i]:
% 32.85/33.05         (~ (r1_tarski @ X4 @ X5)
% 32.85/33.05          | ~ (r1_tarski @ X4 @ X6)
% 32.85/33.05          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 32.85/33.05      inference('cnf', [status(esa)], [t19_xboole_1])).
% 32.85/33.05  thf('10', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ X0)
% 32.85/33.05          | ~ (v1_relat_1 @ X1)
% 32.85/33.05          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 32.85/33.05             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 32.85/33.05          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 32.85/33.05      inference('sup-', [status(thm)], ['8', '9'])).
% 32.85/33.05  thf('11', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ X1)
% 32.85/33.05          | ~ (v1_relat_1 @ X0)
% 32.85/33.05          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 32.85/33.05             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 32.85/33.05          | ~ (v1_relat_1 @ X1)
% 32.85/33.05          | ~ (v1_relat_1 @ X2))),
% 32.85/33.05      inference('sup-', [status(thm)], ['7', '10'])).
% 32.85/33.05  thf('12', plain,
% 32.85/33.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.85/33.05         (~ (v1_relat_1 @ X2)
% 32.85/33.05          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 32.85/33.05             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 32.85/33.05          | ~ (v1_relat_1 @ X0)
% 32.85/33.05          | ~ (v1_relat_1 @ X1))),
% 32.85/33.05      inference('simplify', [status(thm)], ['11'])).
% 32.85/33.05  thf(t52_relat_1, conjecture,
% 32.85/33.05    (![A:$i]:
% 32.85/33.05     ( ( v1_relat_1 @ A ) =>
% 32.85/33.05       ( ![B:$i]:
% 32.85/33.05         ( ( v1_relat_1 @ B ) =>
% 32.85/33.05           ( ![C:$i]:
% 32.85/33.05             ( ( v1_relat_1 @ C ) =>
% 32.85/33.05               ( r1_tarski @
% 32.85/33.05                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 32.85/33.05                 ( k3_xboole_0 @
% 32.85/33.05                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 32.85/33.05  thf(zf_stmt_0, negated_conjecture,
% 32.85/33.05    (~( ![A:$i]:
% 32.85/33.05        ( ( v1_relat_1 @ A ) =>
% 32.85/33.05          ( ![B:$i]:
% 32.85/33.05            ( ( v1_relat_1 @ B ) =>
% 32.85/33.05              ( ![C:$i]:
% 32.85/33.05                ( ( v1_relat_1 @ C ) =>
% 32.85/33.05                  ( r1_tarski @
% 32.85/33.05                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 32.85/33.05                    ( k3_xboole_0 @
% 32.85/33.05                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 32.85/33.05    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 32.85/33.05  thf('13', plain,
% 32.85/33.05      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 32.85/33.05          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 32.85/33.05           (k5_relat_1 @ sk_A @ sk_C)))),
% 32.85/33.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.85/33.05  thf('14', plain,
% 32.85/33.05      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 32.85/33.05      inference('sup-', [status(thm)], ['12', '13'])).
% 32.85/33.05  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 32.85/33.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.85/33.05  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 32.85/33.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.85/33.05  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 32.85/33.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.85/33.05  thf('18', plain, ($false),
% 32.85/33.05      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 32.85/33.05  
% 32.85/33.05  % SZS output end Refutation
% 32.85/33.05  
% 32.85/33.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
