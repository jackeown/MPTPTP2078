%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5zmF91TYb3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:08 EST 2020

% Result     : Theorem 0.32s
% Output     : Refutation 0.32s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  155 ( 162 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ( r2_hidden @ X26 @ X27 )
      | ( X27
       != ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X25: $i,X28: $i] :
      ( r2_hidden @ X25 @ ( k2_tarski @ X28 @ X25 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r2_hidden @ sk_B_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5zmF91TYb3
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.32/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.32/0.51  % Solved by: fo/fo7.sh
% 0.32/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.32/0.51  % done 126 iterations in 0.056s
% 0.32/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.32/0.51  % SZS output start Refutation
% 0.32/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.32/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.32/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.32/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.32/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.32/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.32/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.32/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.32/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.32/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.32/0.51  thf(d3_tarski, axiom,
% 0.32/0.51    (![A:$i,B:$i]:
% 0.32/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.32/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.32/0.51  thf('0', plain,
% 0.32/0.51      (![X4 : $i, X6 : $i]:
% 0.32/0.51         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.32/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.32/0.51  thf(d1_xboole_0, axiom,
% 0.32/0.51    (![A:$i]:
% 0.32/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.32/0.51  thf('1', plain,
% 0.32/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.32/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.32/0.51  thf('2', plain,
% 0.32/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.32/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.32/0.51  thf(t50_zfmisc_1, conjecture,
% 0.32/0.51    (![A:$i,B:$i,C:$i]:
% 0.32/0.51     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.32/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.32/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.32/0.51        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.32/0.51    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.32/0.51  thf('3', plain,
% 0.32/0.51      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1) = (k1_xboole_0))),
% 0.32/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.51  thf(t7_xboole_1, axiom,
% 0.32/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.32/0.51  thf('4', plain,
% 0.32/0.51      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.32/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.32/0.51  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ k1_xboole_0)),
% 0.32/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.32/0.51  thf(d10_xboole_0, axiom,
% 0.32/0.51    (![A:$i,B:$i]:
% 0.32/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.32/0.51  thf('6', plain,
% 0.32/0.51      (![X7 : $i, X9 : $i]:
% 0.32/0.51         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.32/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.32/0.51  thf('7', plain,
% 0.32/0.51      ((~ (r1_tarski @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.32/0.51        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B_1)))),
% 0.32/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.32/0.51  thf('8', plain,
% 0.32/0.51      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.32/0.51        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B_1)))),
% 0.32/0.51      inference('sup-', [status(thm)], ['2', '7'])).
% 0.32/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.32/0.51  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.32/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.32/0.51  thf('10', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.32/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.32/0.51  thf(d2_tarski, axiom,
% 0.32/0.51    (![A:$i,B:$i,C:$i]:
% 0.32/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.32/0.51       ( ![D:$i]:
% 0.32/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.32/0.51  thf('11', plain,
% 0.32/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.32/0.51         (((X26) != (X25))
% 0.32/0.51          | (r2_hidden @ X26 @ X27)
% 0.32/0.51          | ((X27) != (k2_tarski @ X28 @ X25)))),
% 0.32/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.32/0.51  thf('12', plain,
% 0.32/0.51      (![X25 : $i, X28 : $i]: (r2_hidden @ X25 @ (k2_tarski @ X28 @ X25))),
% 0.32/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.32/0.51  thf('13', plain, ((r2_hidden @ sk_B_1 @ k1_xboole_0)),
% 0.32/0.51      inference('sup+', [status(thm)], ['10', '12'])).
% 0.32/0.51  thf('14', plain,
% 0.32/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.32/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.32/0.51  thf('15', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.32/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.32/0.51  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.32/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.32/0.51  thf('17', plain, ($false), inference('demod', [status(thm)], ['15', '16'])).
% 0.32/0.51  
% 0.32/0.51  % SZS output end Refutation
% 0.32/0.51  
% 0.32/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
