%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fDLh322vUt

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 203 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k8_relat_1 @ X8 @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k8_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ X5 @ ( k6_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['2','8'])).

thf(t128_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) )
        = ( k8_relat_1 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) )
          = ( k8_relat_1 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_relat_1])).

thf('10',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_A @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_B )
     != ( k8_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ( k8_relat_1 @ sk_A @ sk_B )
 != ( k8_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fDLh322vUt
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:06:01 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.22/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.44  % Solved by: fo/fo7.sh
% 0.22/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.44  % done 8 iterations in 0.011s
% 0.22/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.44  % SZS output start Refutation
% 0.22/0.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.44  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.44  thf(t116_relat_1, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( v1_relat_1 @ B ) =>
% 0.22/0.44       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.22/0.44  thf('0', plain,
% 0.22/0.44      (![X3 : $i, X4 : $i]:
% 0.22/0.44         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X3 @ X4)) @ X3)
% 0.22/0.44          | ~ (v1_relat_1 @ X4))),
% 0.22/0.44      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.22/0.44  thf(t125_relat_1, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( v1_relat_1 @ B ) =>
% 0.22/0.44       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.44         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.22/0.44  thf('1', plain,
% 0.22/0.44      (![X7 : $i, X8 : $i]:
% 0.22/0.44         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.22/0.44          | ((k8_relat_1 @ X8 @ X7) = (X7))
% 0.22/0.44          | ~ (v1_relat_1 @ X7))),
% 0.22/0.44      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.44  thf('2', plain,
% 0.22/0.44      (![X0 : $i, X1 : $i]:
% 0.22/0.44         (~ (v1_relat_1 @ X1)
% 0.22/0.44          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 0.22/0.44          | ((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1))
% 0.22/0.44              = (k8_relat_1 @ X0 @ X1)))),
% 0.22/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.44  thf(t123_relat_1, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( v1_relat_1 @ B ) =>
% 0.22/0.44       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.22/0.44  thf('3', plain,
% 0.22/0.44      (![X5 : $i, X6 : $i]:
% 0.22/0.44         (((k8_relat_1 @ X6 @ X5) = (k5_relat_1 @ X5 @ (k6_relat_1 @ X6)))
% 0.22/0.44          | ~ (v1_relat_1 @ X5))),
% 0.22/0.44      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.44  thf(dt_k5_relat_1, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.22/0.44       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.22/0.44  thf('4', plain,
% 0.22/0.44      (![X0 : $i, X1 : $i]:
% 0.22/0.44         (~ (v1_relat_1 @ X0)
% 0.22/0.44          | ~ (v1_relat_1 @ X1)
% 0.22/0.44          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.22/0.44      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.44  thf('5', plain,
% 0.22/0.44      (![X0 : $i, X1 : $i]:
% 0.22/0.44         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.44          | ~ (v1_relat_1 @ X0)
% 0.22/0.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.22/0.44          | ~ (v1_relat_1 @ X0))),
% 0.22/0.44      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.44  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.44  thf('6', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.22/0.44      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.44  thf('7', plain,
% 0.22/0.44      (![X0 : $i, X1 : $i]:
% 0.22/0.44         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.44          | ~ (v1_relat_1 @ X0)
% 0.22/0.44          | ~ (v1_relat_1 @ X0))),
% 0.22/0.44      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.44  thf('8', plain,
% 0.22/0.44      (![X0 : $i, X1 : $i]:
% 0.22/0.44         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.22/0.44      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.44  thf('9', plain,
% 0.22/0.44      (![X0 : $i, X1 : $i]:
% 0.22/0.44         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1))
% 0.22/0.44          | ~ (v1_relat_1 @ X1))),
% 0.22/0.44      inference('clc', [status(thm)], ['2', '8'])).
% 0.22/0.44  thf(t128_relat_1, conjecture,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( v1_relat_1 @ B ) =>
% 0.22/0.44       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) ) = ( k8_relat_1 @ A @ B ) ) ))).
% 0.22/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.44    (~( ![A:$i,B:$i]:
% 0.22/0.44        ( ( v1_relat_1 @ B ) =>
% 0.22/0.44          ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) ) =
% 0.22/0.44            ( k8_relat_1 @ A @ B ) ) ) )),
% 0.22/0.44    inference('cnf.neg', [status(esa)], [t128_relat_1])).
% 0.22/0.44  thf('10', plain,
% 0.22/0.44      (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_A @ sk_B))
% 0.22/0.44         != (k8_relat_1 @ sk_A @ sk_B))),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('11', plain,
% 0.22/0.44      ((((k8_relat_1 @ sk_A @ sk_B) != (k8_relat_1 @ sk_A @ sk_B))
% 0.22/0.44        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.44  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('13', plain,
% 0.22/0.44      (((k8_relat_1 @ sk_A @ sk_B) != (k8_relat_1 @ sk_A @ sk_B))),
% 0.22/0.44      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.44  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.22/0.44  
% 0.22/0.44  % SZS output end Refutation
% 0.22/0.44  
% 0.22/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
