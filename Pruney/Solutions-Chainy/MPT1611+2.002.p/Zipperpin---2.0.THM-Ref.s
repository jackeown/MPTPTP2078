%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWubJffQZ8

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  183 ( 208 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

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
    ! [X11: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k9_setfam_1 @ X12 )
      = ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X13 ) @ X13 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X13 ) )
        = ( k3_tarski @ X13 ) )
      | ( v1_xboole_0 @ X13 ) ) ),
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
    ! [X13: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X13 ) )
        = ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X13 ) @ X13 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k9_setfam_1 @ X12 )
      = ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k9_setfam_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k3_yellow_1 @ X14 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('16',plain,(
    ! [X11: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','14','15','16'])).

thf('18',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWubJffQZ8
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 22 iterations in 0.015s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.20/0.47  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.47  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.47  thf(t19_yellow_1, conjecture,
% 0.20/0.47    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.20/0.47  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t99_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.47  thf('1', plain, (![X11 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X11)) = (X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.47  thf(redefinition_k9_setfam_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.47  thf('2', plain, (![X12 : $i]: ((k9_setfam_1 @ X12) = (k1_zfmisc_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('3', plain, (![X11 : $i]: ((k3_tarski @ (k9_setfam_1 @ X11)) = (X11))),
% 0.20/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(t14_yellow_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.20/0.47         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X13 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (k3_tarski @ X13) @ X13)
% 0.20/0.47          | ((k4_yellow_0 @ (k2_yellow_1 @ X13)) = (k3_tarski @ X13))
% 0.20/0.47          | (v1_xboole_0 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.20/0.47  thf(d1_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X13 : $i]:
% 0.20/0.47         (((k4_yellow_0 @ (k2_yellow_1 @ X13)) = (k3_tarski @ X13))
% 0.20/0.47          | ~ (r2_hidden @ (k3_tarski @ X13) @ X13))),
% 0.20/0.47      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.20/0.47          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.20/0.47              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('9', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.20/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.47  thf(d1_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X6 @ X7)
% 0.20/0.47          | (r2_hidden @ X6 @ X8)
% 0.20/0.47          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r2_hidden @ X6 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  thf('12', plain, (![X12 : $i]: ((k9_setfam_1 @ X12) = (k1_zfmisc_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r2_hidden @ X6 @ (k9_setfam_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '13'])).
% 0.20/0.47  thf(t4_yellow_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X14 : $i]: ((k3_yellow_1 @ X14) = (k2_yellow_1 @ (k9_setfam_1 @ X14)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.47  thf('16', plain, (![X11 : $i]: ((k3_tarski @ (k9_setfam_1 @ X11)) = (X11))),
% 0.20/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('17', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '14', '15', '16'])).
% 0.20/0.47  thf('18', plain, (((sk_A) != (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '17'])).
% 0.20/0.47  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
