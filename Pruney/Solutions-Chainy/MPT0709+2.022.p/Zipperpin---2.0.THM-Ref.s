%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JsvPMO6E4Z

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:08 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  324 ( 494 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k9_relat_1 @ X33 @ ( k10_relat_1 @ X33 @ X32 ) )
        = ( k3_xboole_0 @ X32 @ ( k9_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v2_funct_1 @ X36 )
      | ~ ( r1_tarski @ X34 @ ( k1_relat_1 @ X36 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X36 @ X34 ) @ ( k9_relat_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('9',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( r1_tarski @ X28 @ ( k10_relat_1 @ X29 @ ( k9_relat_1 @ X29 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['18','19','20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JsvPMO6E4Z
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:30:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.74/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.92  % Solved by: fo/fo7.sh
% 0.74/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.92  % done 662 iterations in 0.459s
% 0.74/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.92  % SZS output start Refutation
% 0.74/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.74/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.74/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.92  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.74/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.92  thf(t167_relat_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( v1_relat_1 @ B ) =>
% 0.74/0.92       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.74/0.92  thf('0', plain,
% 0.74/0.92      (![X14 : $i, X15 : $i]:
% 0.74/0.92         ((r1_tarski @ (k10_relat_1 @ X14 @ X15) @ (k1_relat_1 @ X14))
% 0.74/0.92          | ~ (v1_relat_1 @ X14))),
% 0.74/0.92      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.74/0.92  thf(t148_funct_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.74/0.92       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.74/0.92         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.74/0.92  thf('1', plain,
% 0.74/0.92      (![X32 : $i, X33 : $i]:
% 0.74/0.92         (((k9_relat_1 @ X33 @ (k10_relat_1 @ X33 @ X32))
% 0.74/0.92            = (k3_xboole_0 @ X32 @ (k9_relat_1 @ X33 @ (k1_relat_1 @ X33))))
% 0.74/0.92          | ~ (v1_funct_1 @ X33)
% 0.74/0.92          | ~ (v1_relat_1 @ X33))),
% 0.74/0.92      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.74/0.92  thf(t17_xboole_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.74/0.92  thf('2', plain,
% 0.74/0.92      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.74/0.92      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.74/0.92  thf('3', plain,
% 0.74/0.92      (![X0 : $i, X1 : $i]:
% 0.74/0.92         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 0.74/0.92          | ~ (v1_relat_1 @ X1)
% 0.74/0.92          | ~ (v1_funct_1 @ X1))),
% 0.74/0.92      inference('sup+', [status(thm)], ['1', '2'])).
% 0.74/0.92  thf(t157_funct_1, axiom,
% 0.74/0.92    (![A:$i,B:$i,C:$i]:
% 0.74/0.92     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.74/0.92       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.74/0.92           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.74/0.92         ( r1_tarski @ A @ B ) ) ))).
% 0.74/0.92  thf('4', plain,
% 0.74/0.92      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.74/0.92         ((r1_tarski @ X34 @ X35)
% 0.74/0.92          | ~ (v1_relat_1 @ X36)
% 0.74/0.92          | ~ (v1_funct_1 @ X36)
% 0.74/0.92          | ~ (v2_funct_1 @ X36)
% 0.74/0.92          | ~ (r1_tarski @ X34 @ (k1_relat_1 @ X36))
% 0.74/0.92          | ~ (r1_tarski @ (k9_relat_1 @ X36 @ X34) @ (k9_relat_1 @ X36 @ X35)))),
% 0.74/0.92      inference('cnf', [status(esa)], [t157_funct_1])).
% 0.74/0.92  thf('5', plain,
% 0.74/0.92      (![X0 : $i, X1 : $i]:
% 0.74/0.92         (~ (v1_funct_1 @ X1)
% 0.74/0.92          | ~ (v1_relat_1 @ X1)
% 0.74/0.92          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 0.74/0.92               (k1_relat_1 @ X1))
% 0.74/0.92          | ~ (v2_funct_1 @ X1)
% 0.74/0.92          | ~ (v1_funct_1 @ X1)
% 0.74/0.92          | ~ (v1_relat_1 @ X1)
% 0.74/0.92          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 0.74/0.92      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.92  thf('6', plain,
% 0.74/0.92      (![X0 : $i, X1 : $i]:
% 0.74/0.92         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 0.74/0.92          | ~ (v2_funct_1 @ X1)
% 0.74/0.92          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 0.74/0.92               (k1_relat_1 @ X1))
% 0.74/0.92          | ~ (v1_relat_1 @ X1)
% 0.74/0.92          | ~ (v1_funct_1 @ X1))),
% 0.74/0.92      inference('simplify', [status(thm)], ['5'])).
% 0.74/0.92  thf('7', plain,
% 0.74/0.92      (![X0 : $i, X1 : $i]:
% 0.74/0.92         (~ (v1_relat_1 @ X0)
% 0.74/0.92          | ~ (v1_funct_1 @ X0)
% 0.74/0.92          | ~ (v1_relat_1 @ X0)
% 0.74/0.92          | ~ (v2_funct_1 @ X0)
% 0.74/0.92          | (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X1))),
% 0.74/0.92      inference('sup-', [status(thm)], ['0', '6'])).
% 0.74/0.92  thf('8', plain,
% 0.74/0.92      (![X0 : $i, X1 : $i]:
% 0.74/0.92         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 0.74/0.92          | ~ (v2_funct_1 @ X0)
% 0.74/0.92          | ~ (v1_funct_1 @ X0)
% 0.74/0.92          | ~ (v1_relat_1 @ X0))),
% 0.74/0.92      inference('simplify', [status(thm)], ['7'])).
% 0.74/0.92  thf(t164_funct_1, conjecture,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.74/0.92       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.74/0.92         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.74/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.92    (~( ![A:$i,B:$i]:
% 0.74/0.92        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.74/0.92          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.74/0.92            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.74/0.92    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.74/0.92  thf('9', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf(t146_funct_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( v1_relat_1 @ B ) =>
% 0.74/0.92       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.74/0.92         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.74/0.92  thf('10', plain,
% 0.74/0.92      (![X28 : $i, X29 : $i]:
% 0.74/0.92         (~ (r1_tarski @ X28 @ (k1_relat_1 @ X29))
% 0.74/0.92          | (r1_tarski @ X28 @ (k10_relat_1 @ X29 @ (k9_relat_1 @ X29 @ X28)))
% 0.74/0.92          | ~ (v1_relat_1 @ X29))),
% 0.74/0.92      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.74/0.92  thf('11', plain,
% 0.74/0.92      ((~ (v1_relat_1 @ sk_B)
% 0.74/0.92        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.74/0.92      inference('sup-', [status(thm)], ['9', '10'])).
% 0.74/0.92  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('13', plain,
% 0.74/0.92      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.74/0.92      inference('demod', [status(thm)], ['11', '12'])).
% 0.74/0.92  thf(d10_xboole_0, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.92  thf('14', plain,
% 0.74/0.92      (![X0 : $i, X2 : $i]:
% 0.74/0.92         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.74/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.92  thf('15', plain,
% 0.74/0.92      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.74/0.92        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['13', '14'])).
% 0.74/0.92  thf('16', plain,
% 0.74/0.92      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('17', plain,
% 0.74/0.92      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.74/0.92      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.74/0.92  thf('18', plain,
% 0.74/0.92      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 0.74/0.92      inference('sup-', [status(thm)], ['8', '17'])).
% 0.74/0.92  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('21', plain, ((v2_funct_1 @ sk_B)),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('22', plain, ($false),
% 0.74/0.92      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.74/0.92  
% 0.74/0.92  % SZS output end Refutation
% 0.74/0.92  
% 0.79/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
