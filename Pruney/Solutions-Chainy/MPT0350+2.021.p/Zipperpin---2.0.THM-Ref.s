%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J4HBk8fcvA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 (  93 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  415 ( 644 expanded)
%              Number of equality atoms :   38 (  62 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('16',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_tarski @ X16 @ X14 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['16','18'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('33',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','28','31','32'])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['11','33'])).

thf('35',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','34'])).

thf('36',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('37',plain,(
    ! [X23: $i] :
      ( ( k2_subset_1 @ X23 )
      = X23 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J4HBk8fcvA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 126 iterations in 0.051s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(t25_subset_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.55         ( k2_subset_1 @ A ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.55            ( k2_subset_1 @ A ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.21/0.55  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_k3_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k3_subset_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))
% 0.21/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.21/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 0.21/0.55          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.55  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d5_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.21/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.55  thf(t39_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.21/0.55           = (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d2_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X20 @ X21)
% 0.21/0.55          | (r2_hidden @ X20 @ X21)
% 0.21/0.55          | (v1_xboole_0 @ X21))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf(fc1_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('15', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('16', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf(d1_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.55          | (r1_tarski @ X16 @ X14)
% 0.21/0.55          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X14 : $i, X16 : $i]:
% 0.21/0.55         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.55  thf('19', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.55  thf(l32_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i, X2 : $i]:
% 0.21/0.55         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.55  thf('21', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.21/0.55           = (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf(commutativity_k2_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.55  thf(l51_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf(t1_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.55  thf('30', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.55  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('33', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['23', '28', '31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['11', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         != (k2_subset_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.55  thf('37', plain, (![X23 : $i]: ((k2_subset_1 @ X23) = (X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain, ($false),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['35', '38'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
