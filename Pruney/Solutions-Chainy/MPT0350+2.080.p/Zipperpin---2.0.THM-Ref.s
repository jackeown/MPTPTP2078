%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMNTIeZVcE

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:56 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  305 ( 461 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X16: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('15',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( r1_tarski @ X5 @ X3 )
      | ( X4
       != ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('20',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','20'])).

thf('22',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('26',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMNTIeZVcE
% 0.16/0.36  % Computer   : n004.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 17:53:09 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 55 iterations in 0.027s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(t25_subset_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.23/0.50         ( k2_subset_1 @ A ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.23/0.50            ( k2_subset_1 @ A ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.23/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(dt_k3_subset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X14 : $i, X15 : $i]:
% 0.23/0.50         ((m1_subset_1 @ (k3_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.23/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d5_subset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X12 : $i, X13 : $i]:
% 0.23/0.50         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.23/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['2', '5'])).
% 0.23/0.50  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(redefinition_k4_subset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.23/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.23/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.23/0.50          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.23/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.23/0.50         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '9'])).
% 0.23/0.50  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d2_subset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X7 @ X8)
% 0.23/0.50          | (r2_hidden @ X7 @ X8)
% 0.23/0.50          | (v1_xboole_0 @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.50        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf(fc1_subset_1, axiom,
% 0.23/0.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.50  thf('14', plain, (![X16 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.23/0.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.50  thf('15', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('clc', [status(thm)], ['13', '14'])).
% 0.23/0.50  thf(d1_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.23/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X5 @ X4)
% 0.23/0.50          | (r1_tarski @ X5 @ X3)
% 0.23/0.51          | ((X4) != (k1_zfmisc_1 @ X3)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X3 : $i, X5 : $i]:
% 0.23/0.51         ((r1_tarski @ X5 @ X3) | ~ (r2_hidden @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.23/0.51  thf('18', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '17'])).
% 0.23/0.51  thf(t45_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.23/0.51       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((X1) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.23/0.51          | ~ (r1_tarski @ X0 @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (((sk_A) = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['10', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.23/0.51         != (k2_subset_1 @ sk_A))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.51  thf('23', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.51  thf('27', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['21', '26'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
