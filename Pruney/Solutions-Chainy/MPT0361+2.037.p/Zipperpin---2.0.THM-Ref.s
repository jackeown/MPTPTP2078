%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i4t0aehFmm

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:55 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  400 ( 740 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X17 @ X16 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('16',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X25 @ X24 ) @ X26 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X25 @ X26 ) @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('29',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','26','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['6','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i4t0aehFmm
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 316 iterations in 0.431s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.68/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(t41_subset_1, conjecture,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ![C:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88           ( r1_tarski @
% 0.68/0.88             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.68/0.88             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i]:
% 0.68/0.88        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88          ( ![C:$i]:
% 0.68/0.88            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88              ( r1_tarski @
% 0.68/0.88                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.68/0.88                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      (~ (r1_tarski @ 
% 0.68/0.88          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.68/0.88          (k3_subset_1 @ sk_A @ sk_B))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k4_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.68/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.68/0.88       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.68/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.68/0.88          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '4'])).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.68/0.88          (k3_subset_1 @ sk_A @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '5'])).
% 0.68/0.88  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(involutiveness_k3_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (![X19 : $i, X20 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.68/0.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.68/0.88      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.88  thf('10', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(dt_k4_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.68/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.68/0.88       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.68/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.68/0.88          | (m1_subset_1 @ (k4_subset_1 @ X17 @ X16 @ X18) @ 
% 0.68/0.88             (k1_zfmisc_1 @ X17)))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.68/0.88           (k1_zfmisc_1 @ sk_A))
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['10', '13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '4'])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf(t36_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ![C:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.68/0.88             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.68/0.88          | (r1_tarski @ (k3_subset_1 @ X25 @ X24) @ X26)
% 0.68/0.88          | ~ (r1_tarski @ (k3_subset_1 @ X25 @ X26) @ X24)
% 0.68/0.88          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.68/0.88          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.68/0.88               (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88          | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.68/0.88             X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['16', '17'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88        | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.68/0.88           (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.88        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['9', '18'])).
% 0.68/0.88  thf(idempotence_k2_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.68/0.88  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.68/0.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.68/0.88  thf(t46_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X8 : $i, X9 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.68/0.88      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.68/0.88  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf(t44_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.68/0.88       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.88         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 0.68/0.88          | ~ (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7))),
% 0.68/0.88      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.68/0.88          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.88  thf('25', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.68/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['24', '25'])).
% 0.68/0.88  thf('27', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(dt_k3_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i]:
% 0.68/0.88         ((m1_subset_1 @ (k3_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.68/0.88          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.68/0.88        (k3_subset_1 @ sk_A @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['19', '26', '29'])).
% 0.68/0.88  thf('31', plain, ($false), inference('demod', [status(thm)], ['6', '30'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
