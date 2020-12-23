%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rmZg2yoE9R

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  153 ( 213 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ X1 )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t46_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t46_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t99_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( v2_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( v2_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t99_funct_1])).

thf('8',plain,(
    ~ ( v2_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['9','10','11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rmZg2yoE9R
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 10 iterations in 0.011s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.46  thf(t123_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         (((k8_relat_1 @ X2 @ X1) = (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)))
% 0.20/0.46          | ~ (v1_relat_1 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.46  thf(t46_funct_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.20/0.46             ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X5)
% 0.20/0.46          | ~ (v1_funct_1 @ X5)
% 0.20/0.46          | (v2_funct_1 @ (k5_relat_1 @ X6 @ X5))
% 0.20/0.46          | ~ (v2_funct_1 @ X5)
% 0.20/0.46          | ~ (v2_funct_1 @ X6)
% 0.20/0.46          | ~ (v1_funct_1 @ X6)
% 0.20/0.46          | ~ (v1_relat_1 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t46_funct_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v2_funct_1 @ X0)
% 0.20/0.46          | ~ (v2_funct_1 @ (k6_relat_1 @ X1))
% 0.20/0.46          | ~ (v1_funct_1 @ (k6_relat_1 @ X1))
% 0.20/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.46  thf('3', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.20/0.46  thf(fc3_funct_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.46  thf('4', plain, (![X4 : $i]: (v1_funct_1 @ (k6_relat_1 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.46  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.46  thf('5', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v2_funct_1 @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v2_funct_1 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (v2_funct_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.46  thf(t99_funct_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46       ( ( v2_funct_1 @ B ) => ( v2_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46          ( ( v2_funct_1 @ B ) => ( v2_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t99_funct_1])).
% 0.20/0.46  thf('8', plain, (~ (v2_funct_1 @ (k8_relat_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('12', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('13', plain, ($false),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
