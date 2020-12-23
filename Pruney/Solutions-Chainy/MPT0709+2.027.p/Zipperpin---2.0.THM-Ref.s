%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p4oVMZ6lQy

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  399 ( 578 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X5 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X3 @ X4 ) @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k2_relat_1 @ X10 ) )
      | ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X13 @ X11 ) @ ( k9_relat_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( r1_tarski @ X7 @ ( k10_relat_1 @ X8 @ ( k9_relat_1 @ X8 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p4oVMZ6lQy
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 71 iterations in 0.044s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.50  thf(t167_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         ((r1_tarski @ (k10_relat_1 @ X5 @ X6) @ (k1_relat_1 @ X5))
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.20/0.50  thf(t144_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         ((r1_tarski @ (k9_relat_1 @ X3 @ X4) @ (k2_relat_1 @ X3))
% 0.20/0.50          | ~ (v1_relat_1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.20/0.50  thf(t147_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.50         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X9 @ (k2_relat_1 @ X10))
% 0.20/0.50          | ((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9)) = (X9))
% 0.20/0.50          | ~ (v1_funct_1 @ X10)
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)))
% 0.20/0.50              = (k9_relat_1 @ X0 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)))
% 0.20/0.50            = (k9_relat_1 @ X0 @ X1))
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.50  thf(t157_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.20/0.50           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.50         ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         ((r1_tarski @ X11 @ X12)
% 0.20/0.50          | ~ (v1_relat_1 @ X13)
% 0.20/0.50          | ~ (v1_funct_1 @ X13)
% 0.20/0.50          | ~ (v2_funct_1 @ X13)
% 0.20/0.50          | ~ (r1_tarski @ X11 @ (k1_relat_1 @ X13))
% 0.20/0.50          | ~ (r1_tarski @ (k9_relat_1 @ X13 @ X11) @ (k9_relat_1 @ X13 @ X12)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t157_funct_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X2))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 0.20/0.50               (k1_relat_1 @ X1))
% 0.20/0.50          | ~ (v2_funct_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X2)
% 0.20/0.50          | ~ (v2_funct_1 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 0.20/0.50               (k1_relat_1 @ X1))
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X2)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k9_relat_1 @ X0 @ X2))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v2_funct_1 @ X0)
% 0.20/0.50          | (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X2)
% 0.20/0.50          | ~ (v2_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k9_relat_1 @ X0 @ X2))
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (v2_funct_1 @ X1)
% 0.20/0.50          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.50  thf(t164_funct_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.20/0.50         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.20/0.50            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.20/0.50  thf('13', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t146_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.50         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X7 @ (k1_relat_1 @ X8))
% 0.20/0.50          | (r1_tarski @ X7 @ (k10_relat_1 @ X8 @ (k9_relat_1 @ X8 @ X7)))
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.20/0.50        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((~ (v2_funct_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '21'])).
% 0.20/0.50  thf('23', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ($false),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
