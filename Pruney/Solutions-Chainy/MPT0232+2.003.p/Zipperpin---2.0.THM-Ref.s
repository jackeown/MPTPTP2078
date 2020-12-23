%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FNdCPhWyOF

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  267 ( 315 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ( r2_hidden @ X21 @ X22 )
      | ( X22
       != ( k2_tarski @ X23 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('6',plain,(
    ! [X20: $i,X23: $i] :
      ( r2_hidden @ X20 @ ( k2_tarski @ X23 @ X20 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( X18 = X15 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_B = sk_C_1 ),
    inference('sup-',[status(thm)],['15','17'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ ( k1_tarski @ X29 ) @ ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['4','18','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FNdCPhWyOF
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:32:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 42 iterations in 0.024s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(t27_zfmisc_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.22/0.47       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.47        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.22/0.47          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d10_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X8 : $i, X10 : $i]:
% 0.22/0.48         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.48        | ((k1_tarski @ sk_C_1) = (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_1))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (~ (r1_tarski @ (k1_tarski @ sk_C_1) @ (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf(d2_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.48       ( ![D:$i]:
% 0.22/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.48         (((X21) != (X20))
% 0.22/0.48          | (r2_hidden @ X21 @ X22)
% 0.22/0.48          | ((X22) != (k2_tarski @ X23 @ X20)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X20 : $i, X23 : $i]: (r2_hidden @ X20 @ (k2_tarski @ X23 @ X20))),
% 0.22/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t28_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X11 : $i, X12 : $i]:
% 0.22/0.48         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.22/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))
% 0.22/0.48         = (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (((k3_xboole_0 @ (k1_tarski @ sk_C_1) @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.48         = (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf(d4_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.22/0.48       ( ![D:$i]:
% 0.22/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.48           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X6 @ X5)
% 0.22/0.48          | (r2_hidden @ X6 @ X3)
% 0.22/0.48          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.22/0.48         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.48          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '13'])).
% 0.22/0.48  thf('15', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_C_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '14'])).
% 0.22/0.48  thf(d1_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X18 @ X17)
% 0.22/0.48          | ((X18) = (X15))
% 0.22/0.48          | ((X17) != (k1_tarski @ X15)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X15 : $i, X18 : $i]:
% 0.22/0.48         (((X18) = (X15)) | ~ (r2_hidden @ X18 @ (k1_tarski @ X15)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.48  thf('18', plain, (((sk_B) = (sk_C_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '17'])).
% 0.22/0.48  thf(commutativity_k2_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i]:
% 0.22/0.48         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.22/0.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.48  thf(t12_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X29 : $i, X30 : $i]:
% 0.22/0.48         (r1_tarski @ (k1_tarski @ X29) @ (k2_tarski @ X29 @ X30))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain, ($false),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '18', '21'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
