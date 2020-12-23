%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ckvjMzZBXc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   98 ( 104 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t67_funct_1,conjecture,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t67_funct_1])).

thf('0',plain,(
    ( k2_funct_1 @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k6_relat_1 @ X0 ) )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X3: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ( k6_relat_1 @ sk_A )
 != ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ckvjMzZBXc
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:12:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 7 iterations in 0.010s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.45  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.19/0.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.45  thf(t67_funct_1, conjecture,
% 0.19/0.45    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t67_funct_1])).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (((k2_funct_1 @ (k6_relat_1 @ sk_A)) != (k6_relat_1 @ sk_A))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(fc3_funct_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.45  thf('1', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.45  thf(d9_funct_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.45       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X1 : $i]:
% 0.19/0.45         (~ (v2_funct_1 @ X1)
% 0.19/0.45          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.19/0.45          | ~ (v1_funct_1 @ X1)
% 0.19/0.45          | ~ (v1_relat_1 @ X1))),
% 0.19/0.45      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.19/0.45          | ((k2_funct_1 @ (k6_relat_1 @ X0))
% 0.19/0.45              = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.19/0.45          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.45  thf('4', plain, (![X3 : $i]: (v1_funct_1 @ (k6_relat_1 @ X3))),
% 0.19/0.45      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf(t72_relat_1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.46  thf(fc4_funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.46  thf('6', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.19/0.46  thf('8', plain, (((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '7'])).
% 0.19/0.46  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
