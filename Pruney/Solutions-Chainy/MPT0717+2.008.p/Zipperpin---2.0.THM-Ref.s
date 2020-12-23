%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UM7ssaF6NT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  343 ( 599 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t172_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v5_relat_1 @ B @ A )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
           => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t172_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ X9 @ X8 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X13 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t73_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X4 ) )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( v5_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v5_relat_1 @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UM7ssaF6NT
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:03:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 28 iterations in 0.026s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.48  thf(t172_funct_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.48           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.48          ( ![C:$i]:
% 0.19/0.48            ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.48              ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t172_funct_1])).
% 0.19/0.48  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t146_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.19/0.48  thf(t94_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]:
% 0.19/0.48         (((k7_relat_1 @ X9 @ X8) = (k5_relat_1 @ (k6_relat_1 @ X8) @ X9))
% 0.19/0.48          | ~ (v1_relat_1 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.48  thf(t160_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( v1_relat_1 @ B ) =>
% 0.19/0.48           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.48             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X1)
% 0.19/0.48          | ((k2_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.19/0.48              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X2)))
% 0.19/0.48          | ~ (v1_relat_1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.48            = (k9_relat_1 @ X1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.19/0.48          | ~ (v1_relat_1 @ X1)
% 0.19/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(t71_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.48  thf('6', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf(fc24_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.19/0.48       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.19/0.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.48  thf('7', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k9_relat_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X1)
% 0.19/0.48          | ~ (v1_relat_1 @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X1)
% 0.19/0.48          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k9_relat_1 @ X1 @ X0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.48  thf('10', plain, ((r2_hidden @ sk_C @ (k1_relat_1 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('11', plain, ((r2_hidden @ sk_C @ (k1_relat_1 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t73_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.19/0.48         ( r2_hidden @
% 0.19/0.48           ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X13 @ X14)
% 0.19/0.48          | ~ (v1_relat_1 @ X15)
% 0.19/0.48          | ~ (v1_funct_1 @ X15)
% 0.19/0.48          | (r2_hidden @ (k1_funct_1 @ X15 @ X13) @ 
% 0.19/0.48             (k2_relat_1 @ (k7_relat_1 @ X15 @ X14)))
% 0.19/0.48          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X15)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t73_funct_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ 
% 0.19/0.48           (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 0.19/0.48          | ~ (v1_funct_1 @ sk_B)
% 0.19/0.48          | ~ (v1_relat_1 @ sk_B)
% 0.19/0.48          | ~ (r2_hidden @ sk_C @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ 
% 0.19/0.48           (k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 0.19/0.48          | ~ (r2_hidden @ sk_C @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ 
% 0.19/0.48        (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (((r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ 
% 0.19/0.48         (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['9', '17'])).
% 0.19/0.48  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ 
% 0.19/0.48        (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (((r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ (k2_relat_1 @ sk_B))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['2', '20'])).
% 0.19/0.48  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ (k2_relat_1 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf(t202_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ (k2_relat_1 @ X4))
% 0.19/0.48          | (r2_hidden @ X3 @ X5)
% 0.19/0.48          | ~ (v5_relat_1 @ X4 @ X5)
% 0.19/0.48          | ~ (v1_relat_1 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ sk_B)
% 0.19/0.48          | ~ (v5_relat_1 @ sk_B @ X0)
% 0.19/0.48          | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v5_relat_1 @ sk_B @ X0)
% 0.19/0.48          | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain, ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_C) @ sk_A)),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '27'])).
% 0.19/0.48  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
