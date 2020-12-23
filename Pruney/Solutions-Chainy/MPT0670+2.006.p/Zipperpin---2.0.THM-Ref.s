%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.erp7pjTdFf

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  377 ( 659 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t87_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
       => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
         => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) @ X6 )
        = ( k1_funct_1 @ X5 @ ( k1_funct_1 @ X4 @ X6 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k1_funct_1 @ ( k6_relat_1 @ X1 ) @ ( k1_funct_1 @ X0 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X3: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k1_funct_1 @ ( k6_relat_1 @ X1 ) @ ( k1_funct_1 @ X0 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k1_funct_1 @ ( k6_relat_1 @ X1 ) @ ( k1_funct_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A )
      = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A )
    = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k8_relat_1 @ X11 @ X10 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X10 @ X9 ) @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t86_funct_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('20',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_C @ sk_A ) )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['12','20'])).

thf('22',plain,
    ( ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.erp7pjTdFf
% 0.13/0.36  % Computer   : n007.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:03:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 20 iterations in 0.015s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.49  thf(t123_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.49  thf(t87_funct_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.21/0.49         ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49          ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.21/0.49            ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) =
% 0.21/0.49              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t87_funct_1])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.49  thf(t22_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.21/0.49             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.21/0.49               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X4 @ X5) @ X6)
% 0.21/0.49              = (k1_funct_1 @ X5 @ (k1_funct_1 @ X4 @ X6)))
% 0.21/0.49          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ (k5_relat_1 @ X4 @ X5)))
% 0.21/0.49          | ~ (v1_funct_1 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X2)
% 0.21/0.49              = (k1_funct_1 @ (k6_relat_1 @ X1) @ (k1_funct_1 @ X0 @ X2)))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(fc3_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('5', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('6', plain, (![X3 : $i]: (v1_funct_1 @ (k6_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X2)
% 0.21/0.49              = (k1_funct_1 @ (k6_relat_1 @ X1) @ (k1_funct_1 @ X0 @ X2)))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X0)
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X2)
% 0.21/0.49              = (k1_funct_1 @ (k6_relat_1 @ X1) @ (k1_funct_1 @ X0 @ X2)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ((k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)
% 0.21/0.49            = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '8'])).
% 0.21/0.49  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)
% 0.21/0.49         = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t86_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.21/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.49           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X9 @ (k1_relat_1 @ (k8_relat_1 @ X11 @ X10)))
% 0.21/0.49          | (r2_hidden @ (k1_funct_1 @ X10 @ X9) @ X11)
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t86_funct_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf(t35_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (k6_relat_1 @ X8) @ X7) = (X7))
% 0.21/0.49          | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ (k1_funct_1 @ sk_C @ sk_A))
% 0.21/0.49         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)
% 0.21/0.49         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.21/0.49          = (k1_funct_1 @ sk_C @ sk_A))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '21'])).
% 0.21/0.49  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.21/0.49         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.21/0.49         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
