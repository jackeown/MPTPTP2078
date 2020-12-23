%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gefu2lTAXH

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:21 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 232 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t152_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( ( k9_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k9_relat_1 @ X7 @ X8 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('5',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['7'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gefu2lTAXH
% 0.15/0.38  % Computer   : n008.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 12:32:45 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.46  % Solved by: fo/fo7.sh
% 0.24/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.46  % done 16 iterations in 0.010s
% 0.24/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.46  % SZS output start Refutation
% 0.24/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.46  thf(t152_relat_1, conjecture,
% 0.24/0.46    (![A:$i,B:$i]:
% 0.24/0.46     ( ( v1_relat_1 @ B ) =>
% 0.24/0.46       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.46            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.24/0.46            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.46    (~( ![A:$i,B:$i]:
% 0.24/0.46        ( ( v1_relat_1 @ B ) =>
% 0.24/0.46          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.46               ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.24/0.46               ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.24/0.46    inference('cnf.neg', [status(esa)], [t152_relat_1])).
% 0.24/0.46  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.46  thf(t28_xboole_1, axiom,
% 0.24/0.46    (![A:$i,B:$i]:
% 0.24/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.46  thf('1', plain,
% 0.24/0.46      (![X5 : $i, X6 : $i]:
% 0.24/0.46         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.24/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.24/0.46  thf('2', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.24/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.46  thf('3', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.46  thf(t151_relat_1, axiom,
% 0.24/0.46    (![A:$i,B:$i]:
% 0.24/0.46     ( ( v1_relat_1 @ B ) =>
% 0.24/0.46       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.46         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.46  thf('4', plain,
% 0.24/0.46      (![X7 : $i, X8 : $i]:
% 0.24/0.46         (((k9_relat_1 @ X7 @ X8) != (k1_xboole_0))
% 0.24/0.46          | (r1_xboole_0 @ (k1_relat_1 @ X7) @ X8)
% 0.24/0.46          | ~ (v1_relat_1 @ X7))),
% 0.24/0.46      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.24/0.46  thf('5', plain,
% 0.24/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.46        | ~ (v1_relat_1 @ sk_B)
% 0.24/0.46        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.24/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.46  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.46  thf('7', plain,
% 0.24/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.46        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.24/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.46  thf('8', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.24/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.46  thf(symmetry_r1_xboole_0, axiom,
% 0.24/0.46    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.24/0.46  thf('9', plain,
% 0.24/0.46      (![X3 : $i, X4 : $i]:
% 0.24/0.46         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.24/0.46      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.24/0.46  thf('10', plain, ((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.24/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.46  thf(d7_xboole_0, axiom,
% 0.24/0.46    (![A:$i,B:$i]:
% 0.24/0.46     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.24/0.46       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.46  thf('11', plain,
% 0.24/0.46      (![X0 : $i, X1 : $i]:
% 0.24/0.46         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.46      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.46  thf('12', plain,
% 0.24/0.46      (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.24/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.46  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.46      inference('sup+', [status(thm)], ['2', '12'])).
% 0.24/0.46  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.46  thf('15', plain, ($false),
% 0.24/0.46      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.24/0.46  
% 0.24/0.46  % SZS output end Refutation
% 0.24/0.46  
% 0.24/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
