%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hFieS8EP7f

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:53 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  438 ( 775 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

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

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('4',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ X14 )
      | ( X16
       != ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( k1_funct_1 @ X14 @ X13 ) ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t74_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) )
    | ( ( k1_funct_1 @ sk_C @ sk_A )
      = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hFieS8EP7f
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:11:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 268 iterations in 0.120s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(fc2_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.38/0.58         ( v1_funct_1 @ B ) ) =>
% 0.38/0.58       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.38/0.58         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i]:
% 0.38/0.58         (~ (v1_funct_1 @ X17)
% 0.38/0.58          | ~ (v1_relat_1 @ X17)
% 0.38/0.58          | ~ (v1_relat_1 @ X18)
% 0.38/0.58          | ~ (v1_funct_1 @ X18)
% 0.38/0.58          | (v1_funct_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.38/0.58  thf(dt_k5_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.38/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X6)
% 0.38/0.58          | ~ (v1_relat_1 @ X7)
% 0.38/0.58          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.38/0.58  thf(t38_funct_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.58       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.38/0.58         ( ( k1_funct_1 @ C @ A ) =
% 0.38/0.58           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.58        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.58          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.38/0.58            ( ( k1_funct_1 @ C @ A ) =
% 0.38/0.58              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(d4_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.38/0.58       ( ![D:$i]:
% 0.38/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.58          | (r2_hidden @ X4 @ X2)
% 0.38/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['3'])).
% 0.38/0.58  thf('5', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.38/0.58      inference('sup-', [status(thm)], ['2', '4'])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.58          | (r2_hidden @ X4 @ X1)
% 0.38/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.58  thf('9', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '8'])).
% 0.38/0.58  thf(d4_funct_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.58       ( ![B:$i,C:$i]:
% 0.38/0.58         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.38/0.58             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.38/0.58               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.58           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.38/0.58             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.38/0.58               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X13 @ X16) @ X14)
% 0.38/0.58          | ((X16) != (k1_funct_1 @ X14 @ X13))
% 0.38/0.58          | ~ (v1_funct_1 @ X14)
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X14)
% 0.38/0.58          | ~ (v1_funct_1 @ X14)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X13 @ (k1_funct_1 @ X14 @ X13)) @ X14)
% 0.38/0.58          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X14)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.38/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '11'])).
% 0.38/0.58  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)),
% 0.38/0.58      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.38/0.58  thf(t74_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ D ) =>
% 0.38/0.58       ( ( r2_hidden @
% 0.38/0.58           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) ) <=>
% 0.38/0.58         ( ( r2_hidden @ A @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X9 @ X10)
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X12)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X9 @ X11) @ 
% 0.38/0.58             (k5_relat_1 @ (k6_relat_1 @ X10) @ X12))
% 0.38/0.58          | ~ (v1_relat_1 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ sk_C)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.38/0.58             (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))
% 0.38/0.58          | ~ (r2_hidden @ sk_A @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.58  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.38/0.58           (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))
% 0.38/0.58          | ~ (r2_hidden @ sk_A @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.38/0.58        (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '19'])).
% 0.38/0.58  thf(t8_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.58       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.38/0.58         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.58           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.58         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 0.38/0.58          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 0.38/0.58          | ~ (v1_funct_1 @ X22)
% 0.38/0.58          | ~ (v1_relat_1 @ X22))),
% 0.38/0.58      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))
% 0.38/0.58        | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))
% 0.38/0.58        | ((k1_funct_1 @ sk_C @ sk_A)
% 0.38/0.58            = (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (((k1_funct_1 @ sk_C @ sk_A)
% 0.38/0.58         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))
% 0.38/0.58        | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C)))),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.58        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.38/0.58        | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '24'])).
% 0.38/0.58  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.38/0.58  thf('27', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))),
% 0.38/0.58      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.58        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.38/0.58        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '28'])).
% 0.38/0.58  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('32', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.58  thf(fc3_funct_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.58       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.58  thf('33', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('34', plain, ($false),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.44/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
