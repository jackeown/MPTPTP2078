%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.si7hREB2FK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  120 ( 186 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(t19_ordinal1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_ordinal1 @ C )
     => ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ B @ C ) )
       => ( r2_hidden @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_ordinal1 @ C )
       => ( ( ( r2_hidden @ A @ B )
            & ( r2_hidden @ B @ C ) )
         => ( r2_hidden @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('3',plain,
    ( ~ ( v1_ordinal1 @ sk_C )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['7','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.si7hREB2FK
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:33:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 38 iterations in 0.027s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.22/0.50  thf(t19_ordinal1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_ordinal1 @ C ) =>
% 0.22/0.50       ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.22/0.50         ( r2_hidden @ A @ C ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( v1_ordinal1 @ C ) =>
% 0.22/0.50          ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.22/0.50            ( r2_hidden @ A @ C ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t19_ordinal1])).
% 0.22/0.50  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d2_ordinal1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_ordinal1 @ A ) <=>
% 0.22/0.50       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X8 @ X9)
% 0.22/0.50          | (r1_tarski @ X8 @ X9)
% 0.22/0.50          | ~ (v1_ordinal1 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.22/0.50  thf('3', plain, ((~ (v1_ordinal1 @ sk_C) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, ((v1_ordinal1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('5', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf(t12_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.50  thf('7', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C) = (sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d3_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X3)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.22/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.50  thf('12', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.22/0.50      inference('sup+', [status(thm)], ['7', '11'])).
% 0.22/0.50  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
