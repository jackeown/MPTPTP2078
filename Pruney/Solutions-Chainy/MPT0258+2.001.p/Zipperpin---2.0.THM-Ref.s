%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jzcq1We0v2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:23 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   70 (  89 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  478 ( 683 expanded)
%              Number of equality atoms :   53 (  70 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t53_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k2_tarski @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ~ ( r2_hidden @ X56 @ X55 )
      | ( ( k2_xboole_0 @ ( k2_tarski @ X54 @ X56 ) @ X55 )
        = X55 ) ) ),
    inference(cnf,[status(esa)],[t48_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_B )
        = sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t101_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ X16 @ X17 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('8',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X31 @ ( k3_xboole_0 @ X31 @ X32 ) )
      = ( k4_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('10',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k5_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','5'])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k5_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ X33 @ ( k4_xboole_0 @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_xboole_0 @ X41 @ X43 )
      | ( ( k4_xboole_0 @ X41 @ X43 )
       != X41 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['15','34'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X4 )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X4 )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jzcq1We0v2
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 282 iterations in 0.132s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.58  thf(t53_zfmisc_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.40/0.58       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.58        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.40/0.58          ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t53_zfmisc_1])).
% 0.40/0.58  thf('0', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t48_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.40/0.58       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X54 @ X55)
% 0.40/0.58          | ~ (r2_hidden @ X56 @ X55)
% 0.40/0.58          | ((k2_xboole_0 @ (k2_tarski @ X54 @ X56) @ X55) = (X55)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t48_zfmisc_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k2_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_B) = (sk_B))
% 0.40/0.58          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf(commutativity_k2_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0)) = (sk_B))
% 0.40/0.58          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) = (sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '5'])).
% 0.40/0.58  thf(t101_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k5_xboole_0 @ A @ B ) =
% 0.40/0.58       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i]:
% 0.40/0.58         ((k5_xboole_0 @ X16 @ X17)
% 0.40/0.58           = (k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.40/0.58              (k3_xboole_0 @ X16 @ X17)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t101_xboole_1])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (((k5_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.40/0.58         = (k4_xboole_0 @ sk_B @ 
% 0.40/0.58            (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf(t47_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X31 : $i, X32 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X31 @ (k3_xboole_0 @ X31 @ X32))
% 0.40/0.58           = (k4_xboole_0 @ X31 @ X32))),
% 0.40/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (((k5_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.40/0.58         = (k4_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.58  thf(t39_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.40/0.58           = (k2_xboole_0 @ X25 @ X26))),
% 0.40/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ 
% 0.40/0.58         (k5_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 0.40/0.58         = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) = (sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '5'])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ 
% 0.40/0.58         (k5_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))) = (sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.40/0.58  thf(t3_boole, axiom,
% 0.40/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.58  thf('16', plain, (![X27 : $i]: ((k4_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.58  thf(t48_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X33 : $i, X34 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X33 @ (k4_xboole_0 @ X33 @ X34))
% 0.40/0.58           = (k3_xboole_0 @ X33 @ X34))),
% 0.40/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('19', plain, (![X27 : $i]: ((k4_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.58  thf(t83_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X41 : $i, X43 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X41 @ X43) | ((k4_xboole_0 @ X41 @ X43) != (X41)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('22', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.40/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.40/0.58  thf(d7_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.40/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['18', '24'])).
% 0.40/0.58  thf(l32_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         ((r1_tarski @ X11 @ X12)
% 0.40/0.58          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.58  thf('28', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.58  thf(t28_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X23 : $i, X24 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.40/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.58  thf('30', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf(t23_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.40/0.58       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.58         ((k3_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 0.40/0.58           = (k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ 
% 0.40/0.58              (k3_xboole_0 @ X20 @ X22)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.40/0.58           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.40/0.58  thf(t22_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X18 : $i, X19 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)) = (X18))),
% 0.40/0.58      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.40/0.58         = (k2_tarski @ sk_A @ sk_C))),
% 0.40/0.58      inference('sup+', [status(thm)], ['15', '34'])).
% 0.40/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i]: ((k3_xboole_0 @ X5 @ X4) = (k3_xboole_0 @ X4 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.40/0.58         = (k2_tarski @ sk_A @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.40/0.58         != (k2_tarski @ sk_A @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i]: ((k3_xboole_0 @ X5 @ X4) = (k3_xboole_0 @ X4 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.40/0.58         != (k2_tarski @ sk_A @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.58  thf('41', plain, ($false),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
