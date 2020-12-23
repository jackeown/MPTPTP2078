%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5jJRt648AW

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:47 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  289 ( 479 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('0',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X42 @ X43 ) ) @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X0 ) )
        = ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X44: $i] :
      ( ( ( k2_relat_1 @ X44 )
       != k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k8_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X40 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t137_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k8_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t137_relat_1])).

thf('21',plain,(
    ( k8_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5jJRt648AW
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 242 iterations in 0.118s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(t116_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (![X42 : $i, X43 : $i]:
% 0.38/0.58         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X42 @ X43)) @ X42)
% 0.38/0.58          | ~ (v1_relat_1 @ X43))),
% 0.38/0.58      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.38/0.58  thf(t28_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.38/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.58  thf(t12_setfam_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X38 : $i, X39 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i]:
% 0.38/0.58         (((k1_setfam_1 @ (k2_tarski @ X8 @ X9)) = (X8))
% 0.38/0.58          | ~ (r1_tarski @ X8 @ X9))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X1)
% 0.38/0.58          | ((k1_setfam_1 @ 
% 0.38/0.58              (k2_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X0))
% 0.38/0.58              = (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '3'])).
% 0.38/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.38/0.58  thf('5', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.58  thf(d1_xboole_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.58  thf(t4_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.38/0.58          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X38 : $i, X39 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 0.38/0.58          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.38/0.58          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '10'])).
% 0.38/0.58  thf(l13_xboole_0, axiom,
% 0.38/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k2_relat_1 @ (k8_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['4', '13'])).
% 0.38/0.58  thf(t64_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.58           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X44 : $i]:
% 0.38/0.58         (((k2_relat_1 @ X44) != (k1_xboole_0))
% 0.38/0.58          | ((X44) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_relat_1 @ X44))),
% 0.38/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ (k8_relat_1 @ k1_xboole_0 @ X0))
% 0.38/0.58          | ((k8_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k8_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_relat_1 @ (k8_relat_1 @ k1_xboole_0 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.58  thf(dt_k8_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X40 : $i, X41 : $i]:
% 0.38/0.58         ((v1_relat_1 @ (k8_relat_1 @ X40 @ X41)) | ~ (v1_relat_1 @ X41))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | ((k8_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.38/0.58      inference('clc', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.58  thf(t137_relat_1, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( v1_relat_1 @ A ) =>
% 0.38/0.58          ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t137_relat_1])).
% 0.38/0.58  thf('21', plain, (((k8_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k8_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.58        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['19', '22'])).
% 0.38/0.58  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '10'])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.58  thf('28', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.38/0.58  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
