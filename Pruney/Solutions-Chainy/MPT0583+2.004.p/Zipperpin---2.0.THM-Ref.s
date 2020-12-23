%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8ux4ePa7WO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:25 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  196 ( 240 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t187_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
           => ( ( k7_relat_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t187_relat_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( ( k7_relat_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k7_relat_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k7_relat_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ( k7_relat_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8ux4ePa7WO
% 0.13/0.37  % Computer   : n004.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:18:24 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 14 iterations in 0.011s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.24/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.50  thf(t187_relat_1, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ A ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.24/0.50           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( ( v1_relat_1 @ A ) =>
% 0.24/0.50          ( ![B:$i]:
% 0.24/0.50            ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.24/0.50              ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t187_relat_1])).
% 0.24/0.50  thf('0', plain, ((r1_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(symmetry_r1_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.24/0.50  thf('2', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)),
% 0.24/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf(d7_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.24/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.50  thf(dt_k7_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X5 : $i, X6 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.24/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.24/0.50  thf(t90_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ B ) =>
% 0.24/0.50       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.24/0.50         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X8 : $i, X9 : $i]:
% 0.24/0.50         (((k1_relat_1 @ (k7_relat_1 @ X8 @ X9))
% 0.24/0.50            = (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9))
% 0.24/0.50          | ~ (v1_relat_1 @ X8))),
% 0.24/0.50      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.24/0.50  thf(t64_relat_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ A ) =>
% 0.24/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.24/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.24/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X7 : $i]:
% 0.24/0.50         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 0.24/0.50          | ((X7) = (k1_xboole_0))
% 0.24/0.50          | ~ (v1_relat_1 @ X7))),
% 0.24/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.24/0.50          | ~ (v1_relat_1 @ X1)
% 0.24/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.24/0.50          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (v1_relat_1 @ X1)
% 0.24/0.50          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.24/0.50          | ~ (v1_relat_1 @ X1)
% 0.24/0.50          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['5', '8'])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.24/0.50          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.24/0.50          | ~ (v1_relat_1 @ X1))),
% 0.24/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.24/0.50        | ((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['4', '10'])).
% 0.24/0.50  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.50        | ((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.24/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.24/0.50  thf('14', plain, (((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.24/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.24/0.50  thf('15', plain, (((k7_relat_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('16', plain, ($false),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
