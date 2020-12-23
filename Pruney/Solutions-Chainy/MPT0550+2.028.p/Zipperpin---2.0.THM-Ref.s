%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W0z0jub2KQ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  200 ( 312 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
        = ( k9_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X4 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X5 @ ( k1_relat_1 @ X6 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W0z0jub2KQ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 12 iterations in 0.012s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(t152_relat_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.48            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.48            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( v1_relat_1 @ B ) =>
% 0.22/0.48          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.48               ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.48               ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t152_relat_1])).
% 0.22/0.48  thf('0', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k7_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.48  thf(t148_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         (((k2_relat_1 @ (k7_relat_1 @ X2 @ X3)) = (k9_relat_1 @ X2 @ X3))
% 0.22/0.48          | ~ (v1_relat_1 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.48  thf(t65_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.48         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X4 : $i]:
% 0.22/0.48         (((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.22/0.48          | ((k1_relat_1 @ X4) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X1)
% 0.22/0.48          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.48          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X1)
% 0.22/0.48          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X1)
% 0.22/0.48          | ((k9_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.48          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X1))),
% 0.22/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.48        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '6'])).
% 0.22/0.48  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('9', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t91_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.48         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (r1_tarski @ X5 @ (k1_relat_1 @ X6))
% 0.22/0.48          | ((k1_relat_1 @ (k7_relat_1 @ X6 @ X5)) = (X5))
% 0.22/0.48          | ~ (v1_relat_1 @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.48        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('13', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.22/0.48  thf('15', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.48  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('17', plain, ($false),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
