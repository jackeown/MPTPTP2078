%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qg54WNqwZo

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  173 ( 257 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k9_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ X9 @ X10 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['10'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','13'])).

thf('15',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qg54WNqwZo
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:41:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 17 iterations in 0.013s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(t7_xboole_0, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.22/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.47  thf(t152_relat_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.47            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.47            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ B ) =>
% 0.22/0.47          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.47               ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.47               ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t152_relat_1])).
% 0.22/0.47  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t28_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X7 : $i, X8 : $i]:
% 0.22/0.47         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.22/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.47  thf('3', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1)) = (sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf(t4_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.22/0.47          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.47          | ~ (r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf('6', plain, (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t151_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.47         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X9 : $i, X10 : $i]:
% 0.22/0.47         (((k9_relat_1 @ X9 @ X10) != (k1_xboole_0))
% 0.22/0.47          | (r1_xboole_0 @ (k1_relat_1 @ X9) @ X10)
% 0.22/0.47          | ~ (v1_relat_1 @ X9))),
% 0.22/0.47      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.47        | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.47        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.47  thf('9', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.47        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.47  thf('11', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.22/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.47  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.47  thf('13', plain, ((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.47  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.22/0.47      inference('demod', [status(thm)], ['5', '13'])).
% 0.22/0.47  thf('15', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '14'])).
% 0.22/0.47  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('17', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
