%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c4cawPJ3TB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  177 ( 221 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k1_wellord1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('2',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_wellord1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_xboole_0 @ ( k1_wellord1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,
    ( ( k1_wellord1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k1_wellord1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c4cawPJ3TB
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 66 iterations in 0.088s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.54  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.21/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(d1_xboole_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf(d1_wellord1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i,C:$i]:
% 0.21/0.54         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.21/0.54           ( ![D:$i]:
% 0.21/0.54             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((X10) != (k1_wellord1 @ X9 @ X8))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X11 @ X8) @ X9)
% 0.21/0.54          | ~ (r2_hidden @ X11 @ X10)
% 0.21/0.54          | ~ (v1_relat_1 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X9)
% 0.21/0.54          | ~ (r2_hidden @ X11 @ (k1_wellord1 @ X9 @ X8))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X11 @ X8) @ X9))),
% 0.21/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (k1_wellord1 @ X1 @ X0))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ (sk_B @ (k1_wellord1 @ X1 @ X0)) @ X0) @ 
% 0.21/0.54             X1)
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '2'])).
% 0.21/0.54  thf(t30_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ C ) =>
% 0.21/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.54         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.54           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.21/0.54          | (r2_hidden @ X5 @ (k3_relat_1 @ X6))
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ (k1_wellord1 @ X0 @ X1))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.21/0.54          | (v1_xboole_0 @ (k1_wellord1 @ X0 @ X1))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.54  thf(t2_wellord1, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.21/0.54         ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( v1_relat_1 @ B ) =>
% 0.21/0.54          ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.21/0.54            ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t2_wellord1])).
% 0.21/0.54  thf('7', plain, (~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B_1) | (v1_xboole_0 @ (k1_wellord1 @ sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('10', plain, ((v1_xboole_0 @ (k1_wellord1 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf(l13_xboole_0, axiom,
% 0.21/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.54  thf('12', plain, (((k1_wellord1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain, (((k1_wellord1 @ sk_B_1 @ sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
