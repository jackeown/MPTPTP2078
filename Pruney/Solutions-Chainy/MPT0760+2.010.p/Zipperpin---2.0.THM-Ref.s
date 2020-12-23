%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qxz9Ak96FY

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:20 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  193 ( 237 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D @ X6 @ X7 @ X8 ) @ X6 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X6 @ X7 @ X8 ) @ X7 ) @ X8 )
      | ( X6
        = ( k1_wellord1 @ X8 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X3 )
      | ( r2_hidden @ X2 @ ( k3_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k1_wellord1 @ X1 @ X2 ) )
      | ( r2_hidden @ X2 @ ( k3_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t2_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
        | ( ( k1_wellord1 @ B @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
          | ( ( k1_wellord1 @ B @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_wellord1])).

thf('8',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( k1_xboole_0
      = ( k1_wellord1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( k1_xboole_0
    = ( k1_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k1_wellord1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qxz9Ak96FY
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:10:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 14 iterations in 0.015s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.19/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.46  thf('0', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.46  thf(d1_wellord1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ![B:$i,C:$i]:
% 0.19/0.46         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.19/0.46           ( ![D:$i]:
% 0.19/0.46             ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.46               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.46         ((r2_hidden @ (sk_D @ X6 @ X7 @ X8) @ X6)
% 0.19/0.46          | (r2_hidden @ (k4_tarski @ (sk_D @ X6 @ X7 @ X8) @ X7) @ X8)
% 0.19/0.46          | ((X6) = (k1_wellord1 @ X8 @ X7))
% 0.19/0.46          | ~ (v1_relat_1 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.19/0.46  thf(t30_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ C ) =>
% 0.19/0.46       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.19/0.46         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.19/0.46           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X3)
% 0.19/0.46          | (r2_hidden @ X2 @ (k3_relat_1 @ X3))
% 0.19/0.46          | ~ (v1_relat_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X0)
% 0.19/0.46          | ((X2) = (k1_wellord1 @ X0 @ X1))
% 0.19/0.46          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.19/0.46          | ~ (v1_relat_1 @ X0)
% 0.19/0.46          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.19/0.46          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.19/0.46          | ((X2) = (k1_wellord1 @ X0 @ X1))
% 0.19/0.46          | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.46  thf(t7_ordinal1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X1)
% 0.19/0.46          | ((X0) = (k1_wellord1 @ X1 @ X2))
% 0.19/0.46          | (r2_hidden @ X2 @ (k3_relat_1 @ X1))
% 0.19/0.46          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X2 @ X1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.19/0.46          | ((k1_xboole_0) = (k1_wellord1 @ X0 @ X1))
% 0.19/0.46          | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '6'])).
% 0.19/0.46  thf(t2_wellord1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.19/0.46         ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ( v1_relat_1 @ B ) =>
% 0.19/0.46          ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.19/0.46            ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t2_wellord1])).
% 0.19/0.46  thf('8', plain, (~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_B) | ((k1_xboole_0) = (k1_wellord1 @ sk_B @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain, (((k1_xboole_0) = (k1_wellord1 @ sk_B @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('12', plain, (((k1_wellord1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('13', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
