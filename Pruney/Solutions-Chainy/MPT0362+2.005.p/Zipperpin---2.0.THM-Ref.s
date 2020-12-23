%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iQntHx2IwV

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:56 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   60 (  72 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  403 ( 558 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3','4'])).

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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( m1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( r1_tarski @ ( k3_subset_1 @ X22 @ X21 ) @ ( k3_subset_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['5','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iQntHx2IwV
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.11  % Solved by: fo/fo7.sh
% 0.91/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.11  % done 1485 iterations in 0.660s
% 0.91/1.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.11  % SZS output start Refutation
% 0.91/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.11  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.91/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.11  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.91/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.11  thf(t42_subset_1, conjecture,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11       ( ![C:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11           ( r1_tarski @
% 0.91/1.11             ( k3_subset_1 @ A @ B ) @ 
% 0.91/1.11             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.11    (~( ![A:$i,B:$i]:
% 0.91/1.11        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11          ( ![C:$i]:
% 0.91/1.11            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11              ( r1_tarski @
% 0.91/1.11                ( k3_subset_1 @ A @ B ) @ 
% 0.91/1.11                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.91/1.11    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.91/1.11  thf('0', plain,
% 0.91/1.11      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.91/1.11          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(redefinition_k9_subset_1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.91/1.11  thf('2', plain,
% 0.91/1.11      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.91/1.11         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.91/1.11          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.91/1.11  thf('3', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         ((k9_subset_1 @ sk_A @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.11  thf(commutativity_k3_xboole_0, axiom,
% 0.91/1.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.91/1.11  thf('4', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.11  thf('5', plain,
% 0.91/1.11      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.91/1.11          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.91/1.11  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(d2_subset_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( v1_xboole_0 @ A ) =>
% 0.91/1.11         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.91/1.11       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.91/1.11         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.91/1.11  thf('7', plain,
% 0.91/1.11      (![X14 : $i, X15 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X14 @ X15)
% 0.91/1.11          | (r2_hidden @ X14 @ X15)
% 0.91/1.11          | (v1_xboole_0 @ X15))),
% 0.91/1.11      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.91/1.11  thf('8', plain,
% 0.91/1.11      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.91/1.11        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.11  thf(fc1_subset_1, axiom,
% 0.91/1.11    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.91/1.11  thf('9', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.91/1.11      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.91/1.11  thf('10', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.11      inference('clc', [status(thm)], ['8', '9'])).
% 0.91/1.11  thf(d1_zfmisc_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.91/1.11       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.91/1.11  thf('11', plain,
% 0.91/1.11      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X12 @ X11)
% 0.91/1.11          | (r1_tarski @ X12 @ X10)
% 0.91/1.11          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.91/1.11      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.91/1.11  thf('12', plain,
% 0.91/1.11      (![X10 : $i, X12 : $i]:
% 0.91/1.11         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.91/1.11      inference('simplify', [status(thm)], ['11'])).
% 0.91/1.11  thf('13', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.91/1.11      inference('sup-', [status(thm)], ['10', '12'])).
% 0.91/1.11  thf(t28_xboole_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.11  thf('14', plain,
% 0.91/1.11      (![X7 : $i, X8 : $i]:
% 0.91/1.11         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.91/1.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.11  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.91/1.11      inference('sup-', [status(thm)], ['13', '14'])).
% 0.91/1.11  thf(t16_xboole_1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.11       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.91/1.11  thf('16', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.11         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.91/1.11           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.91/1.11  thf('17', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.11  thf(t17_xboole_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.91/1.11  thf('18', plain,
% 0.91/1.11      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.91/1.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.91/1.11  thf('19', plain,
% 0.91/1.11      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.91/1.11         (~ (r1_tarski @ X9 @ X10)
% 0.91/1.11          | (r2_hidden @ X9 @ X11)
% 0.91/1.11          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.91/1.11      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.91/1.11  thf('20', plain,
% 0.91/1.11      (![X9 : $i, X10 : $i]:
% 0.91/1.11         ((r2_hidden @ X9 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X9 @ X10))),
% 0.91/1.11      inference('simplify', [status(thm)], ['19'])).
% 0.91/1.11  thf('21', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (r2_hidden @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['18', '20'])).
% 0.91/1.11  thf('22', plain,
% 0.91/1.11      (![X14 : $i, X15 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X14 @ X15)
% 0.91/1.11          | (m1_subset_1 @ X14 @ X15)
% 0.91/1.11          | (v1_xboole_0 @ X15))),
% 0.91/1.11      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.91/1.11  thf('23', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.91/1.11          | (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['21', '22'])).
% 0.91/1.11  thf('24', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.91/1.11      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.91/1.11  thf('25', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.11      inference('clc', [status(thm)], ['23', '24'])).
% 0.91/1.11  thf('26', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['17', '25'])).
% 0.91/1.11  thf('27', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         (m1_subset_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.91/1.11          (k1_zfmisc_1 @ X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['16', '26'])).
% 0.91/1.11  thf('28', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.11      inference('sup+', [status(thm)], ['15', '27'])).
% 0.91/1.11  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(t31_subset_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11       ( ![C:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11           ( ( r1_tarski @ B @ C ) <=>
% 0.91/1.11             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.91/1.11  thf('30', plain,
% 0.91/1.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.91/1.11          | ~ (r1_tarski @ X23 @ X21)
% 0.91/1.11          | (r1_tarski @ (k3_subset_1 @ X22 @ X21) @ (k3_subset_1 @ X22 @ X23))
% 0.91/1.11          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.91/1.11  thf('31', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.91/1.11          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.91/1.11             (k3_subset_1 @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.91/1.11      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.11  thf('32', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 0.91/1.11          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.91/1.11             (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['28', '31'])).
% 0.91/1.11  thf('33', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.11  thf('34', plain,
% 0.91/1.11      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.91/1.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.91/1.11  thf('35', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.11      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.11  thf('36', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.91/1.11          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['32', '35'])).
% 0.91/1.11  thf('37', plain, ($false), inference('demod', [status(thm)], ['5', '36'])).
% 0.91/1.11  
% 0.91/1.11  % SZS output end Refutation
% 0.91/1.11  
% 0.91/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
