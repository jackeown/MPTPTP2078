%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d23XMqcx9P

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:52 EST 2020

% Result     : Theorem 8.48s
% Output     : Refutation 8.48s
% Verified   : 
% Statistics : Number of formulae       :   47 (  66 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  338 ( 589 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t38_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ C @ A )
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['2','6'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k1_funct_1 @ X14 @ ( k1_funct_1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X13: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['2','6'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X18 ) @ X17 )
        = X17 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('17',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d23XMqcx9P
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.48/8.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.48/8.74  % Solved by: fo/fo7.sh
% 8.48/8.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.48/8.74  % done 4128 iterations in 8.292s
% 8.48/8.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.48/8.74  % SZS output start Refutation
% 8.48/8.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 8.48/8.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.48/8.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.48/8.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.48/8.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.48/8.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.48/8.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.48/8.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.48/8.74  thf(sk_A_type, type, sk_A: $i).
% 8.48/8.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.48/8.74  thf(sk_C_type, type, sk_C: $i).
% 8.48/8.74  thf(sk_B_type, type, sk_B: $i).
% 8.48/8.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.48/8.74  thf(t38_funct_1, conjecture,
% 8.48/8.74    (![A:$i,B:$i,C:$i]:
% 8.48/8.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.48/8.74       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 8.48/8.74         ( ( k1_funct_1 @ C @ A ) =
% 8.48/8.74           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 8.48/8.74  thf(zf_stmt_0, negated_conjecture,
% 8.48/8.74    (~( ![A:$i,B:$i,C:$i]:
% 8.48/8.74        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.48/8.74          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 8.48/8.74            ( ( k1_funct_1 @ C @ A ) =
% 8.48/8.74              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 8.48/8.74    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 8.48/8.74  thf('0', plain,
% 8.48/8.74      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 8.48/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.48/8.74  thf(commutativity_k3_xboole_0, axiom,
% 8.48/8.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 8.48/8.74  thf('1', plain,
% 8.48/8.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.48/8.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.48/8.74  thf('2', plain,
% 8.48/8.74      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 8.48/8.74      inference('demod', [status(thm)], ['0', '1'])).
% 8.48/8.74  thf(t48_xboole_1, axiom,
% 8.48/8.74    (![A:$i,B:$i]:
% 8.48/8.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.48/8.74  thf('3', plain,
% 8.48/8.74      (![X8 : $i, X9 : $i]:
% 8.48/8.74         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 8.48/8.74           = (k3_xboole_0 @ X8 @ X9))),
% 8.48/8.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.48/8.74  thf(d5_xboole_0, axiom,
% 8.48/8.74    (![A:$i,B:$i,C:$i]:
% 8.48/8.74     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 8.48/8.74       ( ![D:$i]:
% 8.48/8.74         ( ( r2_hidden @ D @ C ) <=>
% 8.48/8.74           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 8.48/8.74  thf('4', plain,
% 8.48/8.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.48/8.74         (~ (r2_hidden @ X6 @ X5)
% 8.48/8.74          | (r2_hidden @ X6 @ X3)
% 8.48/8.74          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 8.48/8.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 8.48/8.74  thf('5', plain,
% 8.48/8.74      (![X3 : $i, X4 : $i, X6 : $i]:
% 8.48/8.74         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 8.48/8.74      inference('simplify', [status(thm)], ['4'])).
% 8.48/8.74  thf('6', plain,
% 8.48/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.48/8.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 8.48/8.74      inference('sup-', [status(thm)], ['3', '5'])).
% 8.48/8.74  thf('7', plain, ((r2_hidden @ sk_A @ sk_B)),
% 8.48/8.74      inference('sup-', [status(thm)], ['2', '6'])).
% 8.48/8.74  thf(t71_relat_1, axiom,
% 8.48/8.74    (![A:$i]:
% 8.48/8.74     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.48/8.74       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.48/8.74  thf('8', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 8.48/8.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.48/8.74  thf(t23_funct_1, axiom,
% 8.48/8.74    (![A:$i,B:$i]:
% 8.48/8.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.48/8.74       ( ![C:$i]:
% 8.48/8.74         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.48/8.74           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 8.48/8.74             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 8.48/8.74               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 8.48/8.74  thf('9', plain,
% 8.48/8.74      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.48/8.74         (~ (v1_relat_1 @ X14)
% 8.48/8.74          | ~ (v1_funct_1 @ X14)
% 8.48/8.74          | ((k1_funct_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 8.48/8.74              = (k1_funct_1 @ X14 @ (k1_funct_1 @ X15 @ X16)))
% 8.48/8.74          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 8.48/8.74          | ~ (v1_funct_1 @ X15)
% 8.48/8.74          | ~ (v1_relat_1 @ X15))),
% 8.48/8.74      inference('cnf', [status(esa)], [t23_funct_1])).
% 8.48/8.74  thf('10', plain,
% 8.48/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.48/8.74         (~ (r2_hidden @ X1 @ X0)
% 8.48/8.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.48/8.74          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 8.48/8.74          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 8.48/8.74              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 8.48/8.74          | ~ (v1_funct_1 @ X2)
% 8.48/8.74          | ~ (v1_relat_1 @ X2))),
% 8.48/8.74      inference('sup-', [status(thm)], ['8', '9'])).
% 8.48/8.74  thf(fc3_funct_1, axiom,
% 8.48/8.74    (![A:$i]:
% 8.48/8.74     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 8.48/8.74       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 8.48/8.74  thf('11', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 8.48/8.74      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.48/8.74  thf('12', plain, (![X13 : $i]: (v1_funct_1 @ (k6_relat_1 @ X13))),
% 8.48/8.74      inference('cnf', [status(esa)], [fc3_funct_1])).
% 8.48/8.74  thf('13', plain,
% 8.48/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.48/8.74         (~ (r2_hidden @ X1 @ X0)
% 8.48/8.74          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 8.48/8.74              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 8.48/8.74          | ~ (v1_funct_1 @ X2)
% 8.48/8.74          | ~ (v1_relat_1 @ X2))),
% 8.48/8.74      inference('demod', [status(thm)], ['10', '11', '12'])).
% 8.48/8.74  thf('14', plain,
% 8.48/8.74      (![X0 : $i]:
% 8.48/8.74         (~ (v1_relat_1 @ X0)
% 8.48/8.74          | ~ (v1_funct_1 @ X0)
% 8.48/8.74          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 8.48/8.74              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 8.48/8.74      inference('sup-', [status(thm)], ['7', '13'])).
% 8.48/8.74  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 8.48/8.74      inference('sup-', [status(thm)], ['2', '6'])).
% 8.48/8.74  thf(t35_funct_1, axiom,
% 8.48/8.74    (![A:$i,B:$i]:
% 8.48/8.74     ( ( r2_hidden @ A @ B ) =>
% 8.48/8.74       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 8.48/8.74  thf('16', plain,
% 8.48/8.74      (![X17 : $i, X18 : $i]:
% 8.48/8.74         (((k1_funct_1 @ (k6_relat_1 @ X18) @ X17) = (X17))
% 8.48/8.74          | ~ (r2_hidden @ X17 @ X18))),
% 8.48/8.74      inference('cnf', [status(esa)], [t35_funct_1])).
% 8.48/8.74  thf('17', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 8.48/8.74      inference('sup-', [status(thm)], ['15', '16'])).
% 8.48/8.74  thf('18', plain,
% 8.48/8.74      (![X0 : $i]:
% 8.48/8.74         (~ (v1_relat_1 @ X0)
% 8.48/8.74          | ~ (v1_funct_1 @ X0)
% 8.48/8.74          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 8.48/8.74              = (k1_funct_1 @ X0 @ sk_A)))),
% 8.48/8.74      inference('demod', [status(thm)], ['14', '17'])).
% 8.48/8.74  thf('19', plain,
% 8.48/8.74      (((k1_funct_1 @ sk_C @ sk_A)
% 8.48/8.74         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A))),
% 8.48/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.48/8.74  thf('20', plain,
% 8.48/8.74      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 8.48/8.74        | ~ (v1_funct_1 @ sk_C)
% 8.48/8.74        | ~ (v1_relat_1 @ sk_C))),
% 8.48/8.74      inference('sup-', [status(thm)], ['18', '19'])).
% 8.48/8.74  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 8.48/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.48/8.74  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 8.48/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.48/8.74  thf('23', plain,
% 8.48/8.74      (((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))),
% 8.48/8.74      inference('demod', [status(thm)], ['20', '21', '22'])).
% 8.48/8.74  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 8.48/8.74  
% 8.48/8.74  % SZS output end Refutation
% 8.48/8.74  
% 8.48/8.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
