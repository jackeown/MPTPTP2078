%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hC73T6l9Af

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:59 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  181 ( 225 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('8',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ X7 ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t80_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t80_relat_1])).

thf('14',plain,(
    ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hC73T6l9Af
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:26:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.32  % Running in FO mode
% 0.18/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.44  % Solved by: fo/fo7.sh
% 0.18/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.44  % done 13 iterations in 0.013s
% 0.18/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.44  % SZS output start Refutation
% 0.18/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.18/0.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.18/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.44  thf(t71_relat_1, axiom,
% 0.18/0.44    (![A:$i]:
% 0.18/0.44     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.18/0.44       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.18/0.44  thf('0', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.18/0.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.18/0.44  thf(t78_relat_1, axiom,
% 0.18/0.44    (![A:$i]:
% 0.18/0.44     ( ( v1_relat_1 @ A ) =>
% 0.18/0.44       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.18/0.44  thf('1', plain,
% 0.18/0.44      (![X5 : $i]:
% 0.18/0.44         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 0.18/0.44          | ~ (v1_relat_1 @ X5))),
% 0.18/0.44      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.18/0.44  thf('2', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.18/0.44            = (k6_relat_1 @ X0))
% 0.18/0.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.18/0.44      inference('sup+', [status(thm)], ['0', '1'])).
% 0.18/0.44  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.18/0.44  thf('3', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.18/0.44      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.18/0.44  thf('4', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.18/0.44           = (k6_relat_1 @ X0))),
% 0.18/0.44      inference('demod', [status(thm)], ['2', '3'])).
% 0.18/0.44  thf(t44_relat_1, axiom,
% 0.18/0.44    (![A:$i]:
% 0.18/0.44     ( ( v1_relat_1 @ A ) =>
% 0.18/0.44       ( ![B:$i]:
% 0.18/0.44         ( ( v1_relat_1 @ B ) =>
% 0.18/0.44           ( r1_tarski @
% 0.18/0.44             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.18/0.44  thf('5', plain,
% 0.18/0.44      (![X1 : $i, X2 : $i]:
% 0.18/0.44         (~ (v1_relat_1 @ X1)
% 0.18/0.44          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)) @ 
% 0.18/0.44             (k1_relat_1 @ X2))
% 0.18/0.44          | ~ (v1_relat_1 @ X2))),
% 0.18/0.44      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.18/0.44  thf('6', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.18/0.44           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.18/0.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.18/0.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.18/0.44      inference('sup+', [status(thm)], ['4', '5'])).
% 0.18/0.44  thf('7', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.18/0.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.18/0.44  thf('8', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.18/0.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.18/0.44  thf('9', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.18/0.44      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.18/0.44  thf('10', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.18/0.44      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.18/0.44  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.18/0.44      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.18/0.44  thf(t79_relat_1, axiom,
% 0.18/0.44    (![A:$i,B:$i]:
% 0.18/0.44     ( ( v1_relat_1 @ B ) =>
% 0.18/0.44       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.18/0.44         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.18/0.44  thf('12', plain,
% 0.18/0.44      (![X6 : $i, X7 : $i]:
% 0.18/0.44         (~ (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.18/0.44          | ((k5_relat_1 @ X6 @ (k6_relat_1 @ X7)) = (X6))
% 0.18/0.44          | ~ (v1_relat_1 @ X6))),
% 0.18/0.44      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.18/0.44  thf('13', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         (~ (v1_relat_1 @ X0)
% 0.18/0.44          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.18/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.44  thf(t80_relat_1, conjecture,
% 0.18/0.44    (![A:$i]:
% 0.18/0.44     ( ( v1_relat_1 @ A ) =>
% 0.18/0.44       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.18/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.44    (~( ![A:$i]:
% 0.18/0.44        ( ( v1_relat_1 @ A ) =>
% 0.18/0.44          ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ) )),
% 0.18/0.44    inference('cnf.neg', [status(esa)], [t80_relat_1])).
% 0.18/0.44  thf('14', plain,
% 0.18/0.44      (((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_A))) != (sk_A))),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('15', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.18/0.44      inference('sup-', [status(thm)], ['13', '14'])).
% 0.18/0.44  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('17', plain, (((sk_A) != (sk_A))),
% 0.18/0.44      inference('demod', [status(thm)], ['15', '16'])).
% 0.18/0.44  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.18/0.44  
% 0.18/0.44  % SZS output end Refutation
% 0.18/0.44  
% 0.18/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
