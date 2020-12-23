%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.izhU0YCJbO

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  153 ( 193 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t24_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r1_tarski @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
       => ! [C: $i] :
            ( ( r2_hidden @ C @ B )
           => ( r1_tarski @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X9 ) @ ( k3_tarski @ X10 ) )
      | ~ ( r1_setfam_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['3','8'])).

thf('10',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('12',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.izhU0YCJbO
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 14 iterations in 0.011s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(t24_setfam_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.47          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.20/0.47  thf('0', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t18_setfam_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_setfam_1 @ A @ B ) =>
% 0.20/0.47       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         ((r1_tarski @ (k3_tarski @ X9) @ (k3_tarski @ X10))
% 0.20/0.47          | ~ (r1_setfam_1 @ X9 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(t69_enumset1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('4', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf(l51_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.47  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.47  thf('8', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '8'])).
% 0.20/0.47  thf('10', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(l49_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         ((r1_tarski @ X5 @ (k3_tarski @ X6)) | ~ (r2_hidden @ X5 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.47  thf('12', plain, ((r1_tarski @ sk_C @ (k3_tarski @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf(t1_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.47       ( r1_tarski @ A @ C ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X1 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X2 @ X3)
% 0.20/0.47          | (r1_tarski @ X1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ (k3_tarski @ sk_B) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.47  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
