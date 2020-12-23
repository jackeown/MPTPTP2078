%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6TqY7e5aKL

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  24 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  120 ( 164 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_wellord1 @ X4 @ X3 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ X2 )
        = ( k8_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf(t18_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k2_wellord1 @ B @ A )
          = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_wellord1])).

thf('2',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_wellord1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_wellord1 @ sk_B @ sk_A )
     != ( k2_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6TqY7e5aKL
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 4 iterations in 0.008s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.45  thf(t17_wellord1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i]:
% 0.20/0.45         (((k2_wellord1 @ X4 @ X3) = (k7_relat_1 @ (k8_relat_1 @ X3 @ X4) @ X3))
% 0.20/0.45          | ~ (v1_relat_1 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.20/0.45  thf(t140_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ C ) =>
% 0.20/0.45       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.20/0.45         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (((k7_relat_1 @ (k8_relat_1 @ X0 @ X1) @ X2)
% 0.20/0.45            = (k8_relat_1 @ X0 @ (k7_relat_1 @ X1 @ X2)))
% 0.20/0.45          | ~ (v1_relat_1 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.20/0.45  thf(t18_wellord1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( v1_relat_1 @ B ) =>
% 0.20/0.45          ( ( k2_wellord1 @ B @ A ) =
% 0.20/0.45            ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t18_wellord1])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (((k2_wellord1 @ sk_B @ sk_A)
% 0.20/0.45         != (k8_relat_1 @ sk_A @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      ((((k2_wellord1 @ sk_B @ sk_A)
% 0.20/0.45          != (k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.45        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (((k2_wellord1 @ sk_B @ sk_A)
% 0.20/0.45         != (k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      ((((k2_wellord1 @ sk_B @ sk_A) != (k2_wellord1 @ sk_B @ sk_A))
% 0.20/0.45        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.45  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (((k2_wellord1 @ sk_B @ sk_A) != (k2_wellord1 @ sk_B @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
