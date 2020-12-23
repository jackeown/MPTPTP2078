%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8DrMF66hvE

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  219 ( 304 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X22 ) @ ( k3_tarski @ X23 ) )
      | ~ ( r1_setfam_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
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

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X16 )
        = X16 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_C ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X20 ) @ ( k3_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_tarski @ sk_B )
    = ( k2_xboole_0 @ sk_C @ ( k3_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8DrMF66hvE
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 78 iterations in 0.042s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(t24_setfam_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.20/0.50          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.20/0.50  thf('0', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t18_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_setfam_1 @ A @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         ((r1_tarski @ (k3_tarski @ X22) @ (k3_tarski @ X23))
% 0.20/0.50          | ~ (r1_setfam_1 @ X22 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('4', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(l51_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.50  thf('8', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '8'])).
% 0.20/0.50  thf('10', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l22_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.50       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (((k2_xboole_0 @ (k1_tarski @ X17) @ X16) = (X16))
% 0.20/0.50          | ~ (r2_hidden @ X17 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.50  thf('12', plain, (((k2_xboole_0 @ (k1_tarski @ sk_C) @ sk_B) = (sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(t96_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.50       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         ((k3_tarski @ (k2_xboole_0 @ X20 @ X21))
% 0.20/0.50           = (k2_xboole_0 @ (k3_tarski @ X20) @ (k3_tarski @ X21)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k3_tarski @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.20/0.50           = (k2_xboole_0 @ X0 @ (k3_tarski @ X1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((k3_tarski @ sk_B) = (k2_xboole_0 @ sk_C @ (k3_tarski @ sk_B)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '15'])).
% 0.20/0.50  thf(t7_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.50  thf(t1_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.50       ( r1_tarski @ A @ C ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X1 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X2 @ X3)
% 0.20/0.50          | (r1_tarski @ X1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k3_tarski @ sk_B) @ X0) | (r1_tarski @ sk_C @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.50  thf('21', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '20'])).
% 0.20/0.50  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
