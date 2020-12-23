%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IL5MSlIqrL

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  241 ( 361 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t56_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ( ( A != k1_xboole_0 )
           => ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ A )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( ( A != k1_xboole_0 )
             => ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X10 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_tarski @ X2 @ X1 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( m1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IL5MSlIqrL
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:36:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 64 iterations in 0.029s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(t56_subset_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.50           ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.50             ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.50          ( ![C:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.50              ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.50                ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t56_subset_1])).
% 0.22/0.50  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d2_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X14 @ X15)
% 0.22/0.50          | (r2_hidden @ X14 @ X15)
% 0.22/0.50          | (v1_xboole_0 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.50  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X14 @ X15)
% 0.22/0.50          | (r2_hidden @ X14 @ X15)
% 0.22/0.50          | (v1_xboole_0 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.50  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf(t38_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         ((r1_tarski @ (k2_tarski @ X10 @ X12) @ X13)
% 0.22/0.50          | ~ (r2_hidden @ X12 @ X13)
% 0.22/0.50          | ~ (r2_hidden @ X10 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ sk_A)
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.50          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | (r1_tarski @ (k2_tarski @ sk_C_1 @ sk_B) @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '7'])).
% 0.22/0.50  thf(commutativity_k2_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i]: ((k2_tarski @ X2 @ X1) = (k2_tarski @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | (r1_tarski @ (k2_tarski @ sk_B @ sk_C_1) @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((r1_tarski @ (k2_tarski @ sk_B @ sk_C_1) @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.50  thf(d1_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X5 @ X6)
% 0.22/0.50          | (r2_hidden @ X5 @ X7)
% 0.22/0.50          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.22/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | (r2_hidden @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X14 @ X15)
% 0.22/0.50          | (m1_subset_1 @ X14 @ X15)
% 0.22/0.50          | (v1_xboole_0 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.50        | (m1_subset_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf(fc1_subset_1, axiom,
% 0.22/0.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.50  thf('17', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((m1_subset_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.50        | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (~ (m1_subset_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf(l13_xboole_0, axiom,
% 0.22/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.50  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
