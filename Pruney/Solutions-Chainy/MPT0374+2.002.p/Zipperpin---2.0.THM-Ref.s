%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uUcj7toUhQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  285 ( 397 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_B_1 @ sk_A ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X17 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C ) @ sk_A )
      = ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_tarski @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf('22',plain,(
    ~ ( m1_subset_1 @ ( k2_tarski @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uUcj7toUhQ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 107 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(t56_subset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.51           ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.51             ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.51          ( ![C:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.51              ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.51                ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t56_subset_1])).
% 0.21/0.51  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d2_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X21 @ X22)
% 0.21/0.51          | (r2_hidden @ X21 @ X22)
% 0.21/0.51          | (v1_xboole_0 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.51  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X21 @ X22)
% 0.21/0.51          | (r2_hidden @ X21 @ X22)
% 0.21/0.51          | (v1_xboole_0 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.51  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf(t38_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         ((r1_tarski @ (k2_tarski @ X17 @ X19) @ X20)
% 0.21/0.51          | ~ (r2_hidden @ X19 @ X20)
% 0.21/0.51          | ~ (r2_hidden @ X17 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.51          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf(d1_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A) | (r1_tarski @ (k2_tarski @ sk_B_1 @ sk_C) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | ((k3_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C) @ sk_A)
% 0.21/0.51            = (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | ((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.21/0.51            = (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf(t48_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.51           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.51  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X26 : $i, X27 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X26 : $i, X27 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 0.21/0.51           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.51  thf(dt_k6_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i]:
% 0.21/0.51         (m1_subset_1 @ (k6_subset_1 @ X24 @ X25) @ (k1_zfmisc_1 @ X24))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((m1_subset_1 @ (k2_tarski @ sk_B_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['14', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (~ (m1_subset_1 @ (k2_tarski @ sk_B_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf(l13_xboole_0, axiom,
% 0.21/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('25', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
