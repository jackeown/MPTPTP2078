%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lU68O8Pwdz

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:05 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 105 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  359 ( 696 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X23 ) @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = X22 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['22','28'])).

thf('30',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','29'])).

thf('31',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = X22 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('33',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = X22 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lU68O8Pwdz
% 0.14/0.37  % Computer   : n010.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:49:29 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 60 iterations in 0.025s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.23/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(dt_k2_subset_1, axiom,
% 0.23/0.50    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (![X23 : $i]: (m1_subset_1 @ (k2_subset_1 @ X23) @ (k1_zfmisc_1 @ X23))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.23/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.50  thf('1', plain, (![X22 : $i]: ((k2_subset_1 @ X22) = (X22))),
% 0.23/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.50  thf('2', plain, (![X23 : $i]: (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X23))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf(t28_subset_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.23/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(redefinition_k4_subset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.23/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.23/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 0.23/0.50          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.23/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.50  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d2_subset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X19 : $i, X20 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X19 @ X20)
% 0.23/0.50          | (r2_hidden @ X19 @ X20)
% 0.23/0.50          | (v1_xboole_0 @ X20))),
% 0.23/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.50        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf(fc1_subset_1, axiom,
% 0.23/0.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.50  thf('10', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.23/0.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.50  thf('11', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('clc', [status(thm)], ['9', '10'])).
% 0.23/0.50  thf(d1_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.23/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X15 @ X14)
% 0.23/0.50          | (r1_tarski @ X15 @ X13)
% 0.23/0.50          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X13 : $i, X15 : $i]:
% 0.23/0.50         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.23/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.50  thf('14', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '13'])).
% 0.23/0.50  thf(t28_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X4 : $i, X5 : $i]:
% 0.23/0.50         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.23/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.50  thf('16', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.50  thf(t100_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X2 : $i, X3 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ X2 @ X3)
% 0.23/0.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((k4_xboole_0 @ X0 @ X1)
% 0.23/0.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.23/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.50      inference('sup+', [status(thm)], ['16', '19'])).
% 0.23/0.50  thf(t39_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.50  thf('21', plain,
% 0.23/0.50      (![X6 : $i, X7 : $i]:
% 0.23/0.50         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.23/0.50           = (k2_xboole_0 @ X6 @ X7))),
% 0.23/0.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.23/0.50  thf('22', plain,
% 0.23/0.50      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.23/0.50         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.23/0.50      inference('sup+', [status(thm)], ['20', '21'])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.50      inference('sup+', [status(thm)], ['16', '19'])).
% 0.23/0.50  thf(t51_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.23/0.50       ( A ) ))).
% 0.23/0.50  thf('24', plain,
% 0.23/0.50      (![X8 : $i, X9 : $i]:
% 0.23/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X8 @ X9))
% 0.23/0.50           = (X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.23/0.50  thf('25', plain,
% 0.23/0.50      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.23/0.50         (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.23/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.23/0.50  thf('26', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.50  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.50  thf('28', plain,
% 0.23/0.50      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.23/0.50  thf('29', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.23/0.50      inference('sup+', [status(thm)], ['22', '28'])).
% 0.23/0.50  thf('30', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['6', '29'])).
% 0.23/0.50  thf('31', plain,
% 0.23/0.50      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.23/0.50         != (k2_subset_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('32', plain, (![X22 : $i]: ((k2_subset_1 @ X22) = (X22))),
% 0.23/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.50  thf('33', plain, (![X22 : $i]: ((k2_subset_1 @ X22) = (X22))),
% 0.23/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.50  thf('34', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.23/0.50  thf('35', plain, ($false),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['30', '34'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
