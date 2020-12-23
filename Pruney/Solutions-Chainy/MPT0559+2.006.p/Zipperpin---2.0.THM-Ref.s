%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AYhFYszXbo

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  177 ( 199 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X5 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X3 @ X4 ) @ ( k9_relat_1 @ X2 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t161_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t161_relat_1])).

thf('9',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AYhFYszXbo
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 9 iterations in 0.012s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(t94_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         (((k7_relat_1 @ X8 @ X7) = (k5_relat_1 @ (k6_relat_1 @ X7) @ X8))
% 0.20/0.47          | ~ (v1_relat_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.47  thf(t76_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.20/0.47         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X6) @ X5) @ X5)
% 0.20/0.47          | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X1) | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1))),
% 0.20/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.47  thf(t157_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ C ) =>
% 0.20/0.47           ( ( r1_tarski @ B @ C ) =>
% 0.20/0.47             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X2)
% 0.20/0.47          | (r1_tarski @ (k9_relat_1 @ X3 @ X4) @ (k9_relat_1 @ X2 @ X4))
% 0.20/0.47          | ~ (r1_tarski @ X3 @ X2)
% 0.20/0.47          | ~ (v1_relat_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t157_relat_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.47          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.20/0.47             (k9_relat_1 @ X0 @ X2))
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.20/0.47           (k9_relat_1 @ X0 @ X2))
% 0.20/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf(dt_k7_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.20/0.47             (k9_relat_1 @ X0 @ X2)))),
% 0.20/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t161_relat_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( r1_tarski @
% 0.20/0.47         ( k9_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( v1_relat_1 @ C ) =>
% 0.20/0.47          ( r1_tarski @
% 0.20/0.47            ( k9_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) @ 
% 0.20/0.47            ( k9_relat_1 @ C @ B ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t161_relat_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 0.20/0.47          (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain, (~ (v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain, ($false), inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
