%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aqLh8yhPqQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  262 ( 354 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t152_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( ( k9_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('6',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k9_relat_1 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('9',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aqLh8yhPqQ
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 57 iterations in 0.024s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(t152_relat_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.46            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( v1_relat_1 @ B ) =>
% 0.21/0.46          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46               ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.46               ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t152_relat_1])).
% 0.21/0.46  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(l32_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X5 : $i, X7 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf(t48_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.46           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.46         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf(t3_boole, axiom,
% 0.21/0.46    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.46  thf('5', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.46  thf('6', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain, (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t151_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.46         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X15 : $i, X16 : $i]:
% 0.21/0.46         (((k9_relat_1 @ X15 @ X16) != (k1_xboole_0))
% 0.21/0.46          | (r1_xboole_0 @ (k1_relat_1 @ X15) @ X16)
% 0.21/0.46          | ~ (v1_relat_1 @ X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.46        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.46        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.21/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.46  thf(t7_xboole_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.46  thf(t4_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.46            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.46          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (((k3_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.46  thf(commutativity_k2_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X11 : $i, X12 : $i]:
% 0.21/0.46         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.46  thf(t12_setfam_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i]:
% 0.21/0.46         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i]:
% 0.21/0.46         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '21'])).
% 0.21/0.46  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['6', '22'])).
% 0.21/0.46  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('25', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
