%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E7g9CRgN2N

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 (  49 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  240 ( 288 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t207_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_xboole_0 @ A @ B )
         => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t207_relat_1])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( ( k7_relat_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E7g9CRgN2N
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 24 iterations in 0.015s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.47  thf(t87_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ B ) =>
% 0.19/0.47       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i]:
% 0.19/0.47         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X18)) @ X18)
% 0.19/0.47          | ~ (v1_relat_1 @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.19/0.47  thf(t207_relat_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ C ) =>
% 0.19/0.47       ( ( r1_xboole_0 @ A @ B ) =>
% 0.19/0.47         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ( v1_relat_1 @ C ) =>
% 0.19/0.47          ( ( r1_xboole_0 @ A @ B ) =>
% 0.19/0.47            ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t207_relat_1])).
% 0.19/0.47  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t7_xboole_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.47  thf(t4_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.19/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.47  thf(t47_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.19/0.47           = (k4_xboole_0 @ X9 @ X10))),
% 0.19/0.47      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf(t3_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('8', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.47  thf('9', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf(t106_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.47       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.47         ((r1_xboole_0 @ X5 @ X7)
% 0.19/0.47          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ X0)
% 0.19/0.47          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)) @ sk_B_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '11'])).
% 0.19/0.47  thf(t95_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ B ) =>
% 0.19/0.47       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.47         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X19 : $i, X20 : $i]:
% 0.19/0.47         (~ (r1_xboole_0 @ (k1_relat_1 @ X19) @ X20)
% 0.19/0.47          | ((k7_relat_1 @ X19 @ X20) = (k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ X19))),
% 0.19/0.47      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A))
% 0.19/0.47          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf(dt_k7_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X15 : $i, X16 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B_1) = (k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('clc', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (((k7_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('20', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
