%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IY93He06GC

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:57 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  306 ( 489 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X7 ) @ ( k4_xboole_0 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','22'])).

thf('24',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['11','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['4','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IY93He06GC
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 251 iterations in 0.129s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(t42_subset_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ![C:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58           ( r1_tarski @
% 0.38/0.58             ( k3_subset_1 @ A @ B ) @ 
% 0.38/0.58             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i]:
% 0.38/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58          ( ![C:$i]:
% 0.38/0.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58              ( r1_tarski @
% 0.38/0.58                ( k3_subset_1 @ A @ B ) @ 
% 0.38/0.58                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.38/0.58          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(redefinition_k9_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.58         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 0.38/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k9_subset_1 @ sk_A @ X0 @ sk_C) = (k3_xboole_0 @ X0 @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.38/0.58          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.38/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.58  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(dt_k9_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.58         ((m1_subset_1 @ (k9_subset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X13))
% 0.38/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (m1_subset_1 @ (k9_subset_1 @ sk_A @ X0 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k9_subset_1 @ sk_A @ X0 @ sk_C) = (k3_xboole_0 @ X0 @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf(d5_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.38/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))
% 0.38/0.58           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('12', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.38/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf(t48_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X9 : $i, X10 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.38/0.58           = (k3_xboole_0 @ X9 @ X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf(d10_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.58  thf(t106_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.38/0.58       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.58         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.38/0.58      inference('sup+', [status(thm)], ['15', '19'])).
% 0.38/0.58  thf(t34_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.58       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X6 @ X7)
% 0.38/0.58          | (r1_tarski @ (k4_xboole_0 @ X8 @ X7) @ (k4_xboole_0 @ X8 @ X6)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 0.38/0.58          (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.38/0.58          (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['14', '22'])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.38/0.58        (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['11', '23'])).
% 0.38/0.58  thf('25', plain, ($false), inference('demod', [status(thm)], ['4', '24'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
