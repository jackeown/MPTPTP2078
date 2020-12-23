%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c0YfcYlD5u

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  279 ( 313 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ( k6_relat_1 @ sk_A )
 != ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c0YfcYlD5u
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:28:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 21 iterations in 0.021s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.49  thf(t67_funct_1, conjecture,
% 0.21/0.49    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t67_funct_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k2_funct_1 @ (k6_relat_1 @ sk_A)) != (k6_relat_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t71_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.49  thf('1', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.49  thf(dt_k2_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.49         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf(t55_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ A ) =>
% 0.21/0.49         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.49           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X8 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X8)
% 0.21/0.49          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.21/0.49          | ~ (v1_funct_1 @ X8)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.49  thf(t80_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X2 : $i]:
% 0.21/0.49         (((k5_relat_1 @ X2 @ (k6_relat_1 @ (k2_relat_1 @ X2))) = (X2))
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.49            = (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.49              = (k2_funct_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.49            = (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (k2_funct_1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49            = (k2_funct_1 @ (k6_relat_1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '7'])).
% 0.21/0.49  thf(fc3_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('9', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('10', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf(fc4_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('11', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k5_relat_1 @ (k2_funct_1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49           = (k2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.21/0.49  thf(t61_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ A ) =>
% 0.21/0.49         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.21/0.49             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.49           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.21/0.49             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X9)
% 0.21/0.49          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 0.21/0.49              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49            = (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.49  thf('16', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('17', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('18', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.21/0.49  thf('20', plain, (((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '19'])).
% 0.21/0.49  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
