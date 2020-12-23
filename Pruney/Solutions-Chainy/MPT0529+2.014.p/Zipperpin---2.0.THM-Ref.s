%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MqOEbNAemY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  230 ( 349 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X6 @ ( k8_relat_1 @ X7 @ X8 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf(t129_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_relat_1])).

thf('1',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ( k8_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X5 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ~ ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('12',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['4','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MqOEbNAemY
% 0.14/0.37  % Computer   : n019.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 15:03:53 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 19 iterations in 0.017s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.24/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(t127_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ C ) =>
% 0.24/0.50       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.24/0.50         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.50         (((k8_relat_1 @ X6 @ (k8_relat_1 @ X7 @ X8))
% 0.24/0.50            = (k8_relat_1 @ (k3_xboole_0 @ X6 @ X7) @ X8))
% 0.24/0.50          | ~ (v1_relat_1 @ X8))),
% 0.24/0.50      inference('cnf', [status(esa)], [t127_relat_1])).
% 0.24/0.50  thf(t129_relat_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ C ) =>
% 0.24/0.50       ( ( r1_tarski @ A @ B ) =>
% 0.24/0.50         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.50        ( ( v1_relat_1 @ C ) =>
% 0.24/0.50          ( ( r1_tarski @ A @ B ) =>
% 0.24/0.50            ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.24/0.50              ( k8_relat_1 @ A @ C ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t129_relat_1])).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.24/0.50         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      ((((k8_relat_1 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C)
% 0.24/0.50          != (k8_relat_1 @ sk_A @ sk_C))
% 0.24/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (((k8_relat_1 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C)
% 0.24/0.50         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.24/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.24/0.50  thf(d10_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.50  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.24/0.50  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t20_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.24/0.50         ( ![D:$i]:
% 0.24/0.50           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.24/0.50             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.24/0.50       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.50         (~ (r1_tarski @ X3 @ X4)
% 0.24/0.50          | ~ (r1_tarski @ X3 @ X5)
% 0.24/0.50          | (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X5)
% 0.24/0.50          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.24/0.50      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (((sk_A) = (k3_xboole_0 @ sk_B @ X0))
% 0.24/0.50          | (r1_tarski @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.24/0.50          | ~ (r1_tarski @ sk_A @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (((r1_tarski @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)
% 0.24/0.50        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['6', '9'])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.50         (~ (r1_tarski @ X3 @ X4)
% 0.24/0.50          | ~ (r1_tarski @ X3 @ X5)
% 0.24/0.50          | ~ (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X3)
% 0.24/0.50          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.24/0.50      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.24/0.50        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.24/0.50        | ~ (r1_tarski @ sk_A @ sk_A)
% 0.24/0.50        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.24/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.50  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.24/0.50  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('15', plain,
% 0.24/0.50      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.24/0.50        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.24/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.24/0.50  thf('16', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.24/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.24/0.50      inference('demod', [status(thm)], ['4', '16'])).
% 0.24/0.50  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
