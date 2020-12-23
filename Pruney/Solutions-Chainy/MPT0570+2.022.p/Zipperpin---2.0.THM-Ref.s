%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3vmYCOdsFy

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 242 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('1',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k10_relat_1 @ X7 @ X8 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['9'])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['13','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['3','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3vmYCOdsFy
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:57:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 38 iterations in 0.022s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.44  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(l13_xboole_0, axiom,
% 0.20/0.44    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.44  thf(t174_relat_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) =>
% 0.20/0.44       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.44            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.20/0.44            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i]:
% 0.20/0.44        ( ( v1_relat_1 @ B ) =>
% 0.20/0.44          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.44               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.20/0.44               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.20/0.44  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('2', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.44  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.44      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.44  thf('4', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('5', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t173_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) =>
% 0.20/0.44       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.44         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X7 : $i, X8 : $i]:
% 0.20/0.44         (((k10_relat_1 @ X7 @ X8) != (k1_xboole_0))
% 0.20/0.44          | (r1_xboole_0 @ (k2_relat_1 @ X7) @ X8)
% 0.20/0.44          | ~ (v1_relat_1 @ X7))),
% 0.20/0.44      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.44        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.44        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.44  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.44        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('10', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.44      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.44  thf(t68_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.44       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.44            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.44         (~ (r1_xboole_0 @ X4 @ X5)
% 0.20/0.44          | (v1_xboole_0 @ X6)
% 0.20/0.44          | ~ (r1_tarski @ X6 @ X4)
% 0.20/0.44          | ~ (r1_tarski @ X6 @ X5))),
% 0.20/0.44      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.44          | ~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.44          | (v1_xboole_0 @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.44  thf('13', plain, (((v1_xboole_0 @ sk_A) | ~ (r1_tarski @ sk_A @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['4', '12'])).
% 0.20/0.44  thf(d10_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.44  thf('15', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.44      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.44  thf('16', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.44      inference('demod', [status(thm)], ['13', '15'])).
% 0.20/0.44  thf('17', plain, ($false), inference('demod', [status(thm)], ['3', '16'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
