%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CM3jmxoZz2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:28 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  285 ( 337 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t155_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t155_relat_1])).

thf('13',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ ( k9_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CM3jmxoZz2
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.43/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.64  % Solved by: fo/fo7.sh
% 0.43/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.64  % done 263 iterations in 0.188s
% 0.43/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.64  % SZS output start Refutation
% 0.43/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.64  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.43/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.64  thf(t153_relat_1, axiom,
% 0.43/0.64    (![A:$i,B:$i,C:$i]:
% 0.43/0.64     ( ( v1_relat_1 @ C ) =>
% 0.43/0.64       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.43/0.64         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.43/0.64  thf('0', plain,
% 0.43/0.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.64         (((k9_relat_1 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.43/0.64            = (k2_xboole_0 @ (k9_relat_1 @ X13 @ X14) @ 
% 0.43/0.64               (k9_relat_1 @ X13 @ X15)))
% 0.43/0.64          | ~ (v1_relat_1 @ X13))),
% 0.43/0.64      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.43/0.64  thf(d10_xboole_0, axiom,
% 0.43/0.64    (![A:$i,B:$i]:
% 0.43/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.64  thf('1', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.43/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.64  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.43/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.43/0.64  thf(t10_xboole_1, axiom,
% 0.43/0.64    (![A:$i,B:$i,C:$i]:
% 0.43/0.64     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.43/0.64  thf('3', plain,
% 0.43/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.64         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.43/0.64      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.43/0.64  thf('4', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.43/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.64  thf('5', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.64         ((r1_tarski @ (k9_relat_1 @ X2 @ X0) @ 
% 0.43/0.64           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.43/0.64          | ~ (v1_relat_1 @ X2))),
% 0.43/0.64      inference('sup+', [status(thm)], ['0', '4'])).
% 0.43/0.64  thf(t39_xboole_1, axiom,
% 0.43/0.64    (![A:$i,B:$i]:
% 0.43/0.64     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.64  thf('6', plain,
% 0.43/0.64      (![X6 : $i, X7 : $i]:
% 0.43/0.64         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.43/0.64           = (k2_xboole_0 @ X6 @ X7))),
% 0.43/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.43/0.64  thf('7', plain,
% 0.43/0.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.64         (((k9_relat_1 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.43/0.64            = (k2_xboole_0 @ (k9_relat_1 @ X13 @ X14) @ 
% 0.43/0.64               (k9_relat_1 @ X13 @ X15)))
% 0.43/0.64          | ~ (v1_relat_1 @ X13))),
% 0.43/0.64      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.43/0.64  thf(t43_xboole_1, axiom,
% 0.43/0.64    (![A:$i,B:$i,C:$i]:
% 0.43/0.64     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.43/0.64       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.43/0.64  thf('8', plain,
% 0.43/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.43/0.64         ((r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.43/0.64          | ~ (r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.43/0.64      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.43/0.64  thf('9', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.64         (~ (r1_tarski @ X3 @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.43/0.64          | ~ (v1_relat_1 @ X2)
% 0.43/0.64          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.43/0.64             (k9_relat_1 @ X2 @ X0)))),
% 0.43/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.64  thf('10', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.64         (~ (r1_tarski @ X3 @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.43/0.64          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.43/0.64             (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.43/0.64          | ~ (v1_relat_1 @ X2))),
% 0.43/0.64      inference('sup-', [status(thm)], ['6', '9'])).
% 0.43/0.64  thf('11', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.64         (~ (v1_relat_1 @ X2)
% 0.43/0.64          | ~ (v1_relat_1 @ X2)
% 0.43/0.64          | (r1_tarski @ 
% 0.43/0.64             (k4_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.43/0.64             (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.43/0.64      inference('sup-', [status(thm)], ['5', '10'])).
% 0.43/0.64  thf('12', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.64         ((r1_tarski @ 
% 0.43/0.64           (k4_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.43/0.64           (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.43/0.64          | ~ (v1_relat_1 @ X2))),
% 0.43/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.43/0.64  thf(t155_relat_1, conjecture,
% 0.43/0.64    (![A:$i,B:$i,C:$i]:
% 0.43/0.64     ( ( v1_relat_1 @ C ) =>
% 0.43/0.64       ( r1_tarski @
% 0.43/0.64         ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 0.43/0.64         ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ))).
% 0.43/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.64        ( ( v1_relat_1 @ C ) =>
% 0.43/0.64          ( r1_tarski @
% 0.43/0.64            ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 0.43/0.64            ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )),
% 0.43/0.64    inference('cnf.neg', [status(esa)], [t155_relat_1])).
% 0.43/0.64  thf('13', plain,
% 0.43/0.64      (~ (r1_tarski @ 
% 0.43/0.64          (k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.43/0.64           (k9_relat_1 @ sk_C @ sk_B)) @ 
% 0.43/0.64          (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.43/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.64  thf(redefinition_k6_subset_1, axiom,
% 0.43/0.64    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.43/0.64  thf('14', plain,
% 0.43/0.64      (![X11 : $i, X12 : $i]:
% 0.43/0.64         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.43/0.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.64  thf('15', plain,
% 0.43/0.64      (![X11 : $i, X12 : $i]:
% 0.43/0.64         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.43/0.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.64  thf('16', plain,
% 0.43/0.64      (~ (r1_tarski @ 
% 0.43/0.64          (k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.43/0.64           (k9_relat_1 @ sk_C @ sk_B)) @ 
% 0.43/0.64          (k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.64      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.43/0.64  thf('17', plain, (~ (v1_relat_1 @ sk_C)),
% 0.43/0.64      inference('sup-', [status(thm)], ['12', '16'])).
% 0.43/0.64  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.64  thf('19', plain, ($false), inference('demod', [status(thm)], ['17', '18'])).
% 0.43/0.64  
% 0.43/0.64  % SZS output end Refutation
% 0.43/0.64  
% 0.43/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
