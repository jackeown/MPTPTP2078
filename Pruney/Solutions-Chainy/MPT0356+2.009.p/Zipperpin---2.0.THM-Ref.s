%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H6PPKjnUPe

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:18 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   56 (  72 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  332 ( 537 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_tarski @ X18 @ X16 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['11','17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['18','25'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X14 )
      | ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H6PPKjnUPe
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:46:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 518 iterations in 0.232s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(t35_subset_1, conjecture,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ![C:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.46/0.69             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i]:
% 0.46/0.69        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69          ( ![C:$i]:
% 0.46/0.69            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.46/0.69                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 0.46/0.69  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d2_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.69       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (![X20 : $i, X21 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X20 @ X21)
% 0.46/0.69          | (r2_hidden @ X20 @ X21)
% 0.46/0.69          | (v1_xboole_0 @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.69        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.69  thf(fc1_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.69  thf('4', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['3', '4'])).
% 0.46/0.69  thf(d1_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X18 @ X17)
% 0.46/0.69          | (r1_tarski @ X18 @ X16)
% 0.46/0.69          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      (![X16 : $i, X18 : $i]:
% 0.46/0.69         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.69  thf('8', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['5', '7'])).
% 0.46/0.69  thf('9', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d5_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.69  thf('10', plain,
% 0.46/0.69      (![X23 : $i, X24 : $i]:
% 0.46/0.69         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.46/0.69          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.69  thf('11', plain,
% 0.46/0.69      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.69  thf(d10_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.69  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.69  thf(t85_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X9 @ X10)
% 0.46/0.69          | (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.69  thf(t83_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X6 : $i, X7 : $i]:
% 0.46/0.69         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (((k4_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['11', '17'])).
% 0.46/0.69  thf('19', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X9 @ X10)
% 0.46/0.69          | (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (r1_xboole_0 @ sk_B @ 
% 0.46/0.69          (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X6 : $i, X7 : $i]:
% 0.46/0.69         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.69  thf('23', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ sk_B @ 
% 0.46/0.69           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))) = (sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)) @ 
% 0.46/0.69          sk_B)),
% 0.46/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.69  thf('26', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.46/0.69      inference('sup+', [status(thm)], ['18', '25'])).
% 0.46/0.69  thf(t86_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.46/0.69       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X12 @ X13)
% 0.46/0.69          | ~ (r1_xboole_0 @ X12 @ X14)
% 0.46/0.69          | (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_B))
% 0.46/0.69          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.69  thf('29', plain, ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['8', '28'])).
% 0.46/0.69  thf('30', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      (![X23 : $i, X24 : $i]:
% 0.46/0.69         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.46/0.69          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.69  thf('32', plain,
% 0.46/0.69      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.69  thf('33', plain, ((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['29', '32'])).
% 0.46/0.69  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
