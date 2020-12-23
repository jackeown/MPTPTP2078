%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nz0AB5nmkm

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:53 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  340 ( 557 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
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

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X13 @ X12 ) @ X14 )
        = ( k1_funct_1 @ X12 @ ( k1_funct_1 @ X13 @ X14 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k6_relat_1 @ X15 ) )
      | ( ( k1_funct_1 @ X16 @ X17 )
        = X17 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('13',plain,(
    ! [X15: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X15 ) @ X17 )
        = X17 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X15: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X15 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X15 ) @ X17 )
        = X17 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_A )
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nz0AB5nmkm
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 403 iterations in 0.243s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.70  thf(t38_funct_1, conjecture,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.70       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.47/0.70         ( ( k1_funct_1 @ C @ A ) =
% 0.47/0.70           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.70        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.70          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.47/0.70            ( ( k1_funct_1 @ C @ A ) =
% 0.47/0.70              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.47/0.70  thf('0', plain,
% 0.47/0.70      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(d4_xboole_0, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.47/0.70       ( ![D:$i]:
% 0.47/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.70           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X4 @ X3)
% 0.47/0.70          | (r2_hidden @ X4 @ X2)
% 0.47/0.70          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.70         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.47/0.70      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.70  thf('3', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.47/0.70      inference('sup-', [status(thm)], ['0', '2'])).
% 0.47/0.70  thf(t71_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.70  thf('4', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.70  thf(t23_funct_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.70       ( ![C:$i]:
% 0.47/0.70         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.70           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.70             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.47/0.70               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X12)
% 0.47/0.70          | ~ (v1_funct_1 @ X12)
% 0.47/0.70          | ((k1_funct_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 0.47/0.70              = (k1_funct_1 @ X12 @ (k1_funct_1 @ X13 @ X14)))
% 0.47/0.70          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.47/0.70          | ~ (v1_funct_1 @ X13)
% 0.47/0.70          | ~ (v1_relat_1 @ X13))),
% 0.47/0.70      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X1 @ X0)
% 0.47/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.47/0.70          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.47/0.70              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.47/0.70          | ~ (v1_funct_1 @ X2)
% 0.47/0.70          | ~ (v1_relat_1 @ X2))),
% 0.47/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.70  thf(fc3_funct_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.70  thf('7', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('8', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X1 @ X0)
% 0.47/0.70          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.47/0.70              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.47/0.70          | ~ (v1_funct_1 @ X2)
% 0.47/0.70          | ~ (v1_relat_1 @ X2))),
% 0.47/0.70      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.47/0.70  thf('10', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | ~ (v1_funct_1 @ X0)
% 0.47/0.70          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.47/0.70              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['3', '9'])).
% 0.47/0.70  thf('11', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.47/0.70      inference('sup-', [status(thm)], ['0', '2'])).
% 0.47/0.70  thf(t34_funct_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.70       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.47/0.70         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.70         (((X16) != (k6_relat_1 @ X15))
% 0.47/0.70          | ((k1_funct_1 @ X16 @ X17) = (X17))
% 0.47/0.70          | ~ (r2_hidden @ X17 @ X15)
% 0.47/0.70          | ~ (v1_funct_1 @ X16)
% 0.47/0.70          | ~ (v1_relat_1 @ X16))),
% 0.47/0.70      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.47/0.70  thf('13', plain,
% 0.47/0.70      (![X15 : $i, X17 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ (k6_relat_1 @ X15))
% 0.47/0.70          | ~ (v1_funct_1 @ (k6_relat_1 @ X15))
% 0.47/0.70          | ~ (r2_hidden @ X17 @ X15)
% 0.47/0.70          | ((k1_funct_1 @ (k6_relat_1 @ X15) @ X17) = (X17)))),
% 0.47/0.70      inference('simplify', [status(thm)], ['12'])).
% 0.47/0.70  thf('14', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('15', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('16', plain,
% 0.47/0.70      (![X15 : $i, X17 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X17 @ X15)
% 0.47/0.70          | ((k1_funct_1 @ (k6_relat_1 @ X15) @ X17) = (X17)))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.70  thf('17', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['11', '16'])).
% 0.47/0.70  thf('18', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | ~ (v1_funct_1 @ X0)
% 0.47/0.70          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.47/0.70              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.47/0.70      inference('demod', [status(thm)], ['10', '17'])).
% 0.47/0.70  thf('19', plain,
% 0.47/0.70      (((k1_funct_1 @ sk_C_1 @ sk_A)
% 0.47/0.70         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C_1) @ sk_A))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      ((((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))
% 0.47/0.70        | ~ (v1_funct_1 @ sk_C_1)
% 0.47/0.70        | ~ (v1_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      (((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.47/0.70  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
