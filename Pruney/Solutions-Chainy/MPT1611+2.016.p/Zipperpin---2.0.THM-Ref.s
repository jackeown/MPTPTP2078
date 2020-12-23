%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.klWuri0wi1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  54 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :  222 ( 247 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(t19_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_1])).

thf('0',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X15 ) @ X15 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X15 ) )
        = ( k3_tarski @ X15 ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X15: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X15 ) )
        = ( k3_tarski @ X15 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X15 ) @ X15 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('9',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ ( k1_zfmisc_1 @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('12',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ ( k9_setfam_1 @ ( k3_tarski @ X12 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','20'])).

thf('22',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.klWuri0wi1
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:05:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 24 iterations in 0.014s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.48  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.48  thf(t19_yellow_1, conjecture,
% 0.21/0.48    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.21/0.48  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t99_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.48  thf('1', plain, (![X13 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X13)) = (X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.48  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.48  thf('2', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.48  thf('3', plain, (![X13 : $i]: ((k3_tarski @ (k9_setfam_1 @ X13)) = (X13))),
% 0.21/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf(t14_yellow_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.21/0.48         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X15 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k3_tarski @ X15) @ X15)
% 0.21/0.48          | ((k4_yellow_0 @ (k2_yellow_1 @ X15)) = (k3_tarski @ X15))
% 0.21/0.48          | (v1_xboole_0 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X15 : $i]:
% 0.21/0.48         (((k4_yellow_0 @ (k2_yellow_1 @ X15)) = (k3_tarski @ X15))
% 0.21/0.48          | ~ (r2_hidden @ (k3_tarski @ X15) @ X15))),
% 0.21/0.48      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.48          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.21/0.48              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.48  thf(t4_yellow_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k2_yellow_1 @ (k9_setfam_1 @ X16)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.48  thf('9', plain, (![X13 : $i]: ((k3_tarski @ (k9_setfam_1 @ X13)) = (X13))),
% 0.21/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.48          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.48  thf(t100_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X12 : $i]: (r1_tarski @ X12 @ (k1_zfmisc_1 @ (k3_tarski @ X12)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.21/0.48  thf('12', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X12 : $i]: (r1_tarski @ X12 @ (k9_setfam_1 @ (k3_tarski @ X12)))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('14', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(l1_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k2_tarski @ X0 @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (r2_hidden @ X0 @ (k9_setfam_1 @ (k3_tarski @ (k2_tarski @ X0 @ X0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.48  thf(l51_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.48  thf('19', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.48  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.48  thf('21', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '20'])).
% 0.21/0.48  thf('22', plain, (((sk_A) != (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '21'])).
% 0.21/0.48  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
