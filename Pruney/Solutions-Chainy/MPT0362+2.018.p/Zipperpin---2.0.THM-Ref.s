%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C1EJtYbcyM

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:58 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   57 (  68 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 ( 526 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t42_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( m1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( r1_tarski @ ( k3_subset_1 @ X22 @ X21 ) @ ( k3_subset_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['4','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C1EJtYbcyM
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 156 iterations in 0.095s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.57  thf(t42_subset_1, conjecture,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57       ( ![C:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57           ( r1_tarski @
% 0.40/0.57             ( k3_subset_1 @ A @ B ) @ 
% 0.40/0.57             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i,B:$i]:
% 0.40/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57          ( ![C:$i]:
% 0.40/0.57            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57              ( r1_tarski @
% 0.40/0.57                ( k3_subset_1 @ A @ B ) @ 
% 0.40/0.57                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.57          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(redefinition_k9_subset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.40/0.57  thf('2', plain,
% 0.40/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.57         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.40/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((k9_subset_1 @ sk_A @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.57  thf('4', plain,
% 0.40/0.57      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.57          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.40/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.40/0.57  thf(t48_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.57  thf('5', plain,
% 0.40/0.57      (![X7 : $i, X8 : $i]:
% 0.40/0.57         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.40/0.57           = (k3_xboole_0 @ X7 @ X8))),
% 0.40/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.57  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(d2_subset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.40/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.40/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      (![X14 : $i, X15 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X14 @ X15)
% 0.40/0.57          | (r2_hidden @ X14 @ X15)
% 0.40/0.57          | (v1_xboole_0 @ X15))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.57        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.57  thf(fc1_subset_1, axiom,
% 0.40/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.57  thf('9', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.40/0.57  thf('10', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.57      inference('clc', [status(thm)], ['8', '9'])).
% 0.40/0.57  thf(d1_zfmisc_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.57  thf('11', plain,
% 0.40/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X12 @ X11)
% 0.40/0.57          | (r1_tarski @ X12 @ X10)
% 0.40/0.57          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.57  thf('12', plain,
% 0.40/0.57      (![X10 : $i, X12 : $i]:
% 0.40/0.57         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.57  thf('13', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.40/0.57      inference('sup-', [status(thm)], ['10', '12'])).
% 0.40/0.57  thf(t36_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.40/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.57  thf(t1_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.40/0.57       ( r1_tarski @ A @ C ) ))).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.57         (~ (r1_tarski @ X2 @ X3)
% 0.40/0.57          | ~ (r1_tarski @ X3 @ X4)
% 0.40/0.57          | (r1_tarski @ X2 @ X4))),
% 0.40/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.40/0.57      inference('sup-', [status(thm)], ['13', '16'])).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.57         (~ (r1_tarski @ X9 @ X10)
% 0.40/0.57          | (r2_hidden @ X9 @ X11)
% 0.40/0.57          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X9 : $i, X10 : $i]:
% 0.40/0.57         ((r2_hidden @ X9 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X9 @ X10))),
% 0.40/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (r2_hidden @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['17', '19'])).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      (![X14 : $i, X15 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X14 @ X15)
% 0.40/0.57          | (m1_subset_1 @ X14 @ X15)
% 0.40/0.57          | (v1_xboole_0 @ X15))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.57          | (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.57  thf('23', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.57      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.57      inference('sup+', [status(thm)], ['5', '24'])).
% 0.40/0.57  thf('26', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(t31_subset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57       ( ![C:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57           ( ( r1_tarski @ B @ C ) <=>
% 0.40/0.57             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.57  thf('27', plain,
% 0.40/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.40/0.57          | ~ (r1_tarski @ X23 @ X21)
% 0.40/0.57          | (r1_tarski @ (k3_subset_1 @ X22 @ X21) @ (k3_subset_1 @ X22 @ X23))
% 0.40/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.57          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.57             (k3_subset_1 @ sk_A @ X0))
% 0.40/0.57          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.40/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.40/0.57          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.57             (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['25', '28'])).
% 0.40/0.57  thf('30', plain,
% 0.40/0.57      (![X7 : $i, X8 : $i]:
% 0.40/0.57         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.40/0.57           = (k3_xboole_0 @ X7 @ X8))),
% 0.40/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.40/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.57  thf('32', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.40/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.40/0.57  thf('33', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.57          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.40/0.57      inference('demod', [status(thm)], ['29', '32'])).
% 0.40/0.57  thf('34', plain, ($false), inference('demod', [status(thm)], ['4', '33'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
