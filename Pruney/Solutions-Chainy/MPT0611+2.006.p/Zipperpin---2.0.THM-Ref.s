%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QJUGosO0OG

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  70 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 ( 520 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t215_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t215_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t27_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X12 @ X11 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X12 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t27_relat_1])).

thf('6',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 )
      | ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 )
      | ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','16'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( ( k2_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QJUGosO0OG
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.42  % Solved by: fo/fo7.sh
% 0.20/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.42  % done 36 iterations in 0.013s
% 0.20/0.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.42  % SZS output start Refutation
% 0.20/0.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.42  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.42  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.42  thf(t215_relat_1, conjecture,
% 0.20/0.42    (![A:$i]:
% 0.20/0.42     ( ( v1_relat_1 @ A ) =>
% 0.20/0.42       ( ![B:$i]:
% 0.20/0.42         ( ( v1_relat_1 @ B ) =>
% 0.20/0.42           ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.42             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.20/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.42    (~( ![A:$i]:
% 0.20/0.42        ( ( v1_relat_1 @ A ) =>
% 0.20/0.42          ( ![B:$i]:
% 0.20/0.42            ( ( v1_relat_1 @ B ) =>
% 0.20/0.42              ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.42                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.20/0.42    inference('cnf.neg', [status(esa)], [t215_relat_1])).
% 0.20/0.42  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.42  thf(fc1_relat_1, axiom,
% 0.20/0.42    (![A:$i,B:$i]:
% 0.20/0.42     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.42  thf('1', plain,
% 0.20/0.42      (![X9 : $i, X10 : $i]:
% 0.20/0.42         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.20/0.42      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.20/0.42  thf('2', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.42  thf(d7_xboole_0, axiom,
% 0.20/0.42    (![A:$i,B:$i]:
% 0.20/0.42     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.42       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.42  thf('3', plain,
% 0.20/0.42      (![X0 : $i, X1 : $i]:
% 0.20/0.42         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.42      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (((k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.20/0.43         = (k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.43  thf(t27_relat_1, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ A ) =>
% 0.20/0.43       ( ![B:$i]:
% 0.20/0.43         ( ( v1_relat_1 @ B ) =>
% 0.20/0.43           ( r1_tarski @
% 0.20/0.43             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.20/0.43             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X11 : $i, X12 : $i]:
% 0.20/0.43         (~ (v1_relat_1 @ X11)
% 0.20/0.43          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X12 @ X11)) @ 
% 0.20/0.43             (k3_xboole_0 @ (k2_relat_1 @ X12) @ (k2_relat_1 @ X11)))
% 0.20/0.43          | ~ (v1_relat_1 @ X12))),
% 0.20/0.43      inference('cnf', [status(esa)], [t27_relat_1])).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)
% 0.20/0.43        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.43        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.43      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.43  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)),
% 0.20/0.43      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.43  thf('10', plain,
% 0.20/0.43      ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ k1_xboole_0)),
% 0.20/0.43      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.43  thf(t67_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.20/0.43         ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.43       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.43         (((X6) = (k1_xboole_0))
% 0.20/0.43          | ~ (r1_tarski @ X6 @ X7)
% 0.20/0.43          | ~ (r1_tarski @ X6 @ X8)
% 0.20/0.43          | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.20/0.43      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.20/0.43  thf('12', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.43          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0)
% 0.20/0.43          | ((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.43  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.43  thf('13', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.43      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.43  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (![X3 : $i, X4 : $i]:
% 0.20/0.43         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.43  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.43      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.43  thf('16', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0)
% 0.20/0.43          | ((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.43      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.43  thf('17', plain,
% 0.20/0.43      (((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.43  thf(t64_relat_1, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ A ) =>
% 0.20/0.43       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.43           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.43         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.43  thf('18', plain,
% 0.20/0.43      (![X13 : $i]:
% 0.20/0.43         (((k2_relat_1 @ X13) != (k1_xboole_0))
% 0.20/0.43          | ((X13) = (k1_xboole_0))
% 0.20/0.43          | ~ (v1_relat_1 @ X13))),
% 0.20/0.43      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.43  thf('19', plain,
% 0.20/0.43      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.43        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.20/0.43        | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.43  thf('20', plain,
% 0.20/0.43      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.43        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.43      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.43  thf('21', plain,
% 0.20/0.43      ((~ (v1_relat_1 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['1', '20'])).
% 0.20/0.43  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('23', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.43      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.43  thf('24', plain,
% 0.20/0.43      (![X0 : $i, X2 : $i]:
% 0.20/0.43         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.43      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.43  thf('25', plain,
% 0.20/0.43      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.43  thf('26', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.43      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.43  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
