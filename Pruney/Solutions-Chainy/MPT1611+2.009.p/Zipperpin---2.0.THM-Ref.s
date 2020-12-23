%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fcJRTm5Nd0

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  192 ( 217 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X10: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k9_setfam_1 @ X11 )
      = ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X12 ) @ X12 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X12 ) )
        = ( k3_tarski @ X12 ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('6',plain,(
    ! [X12: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X12 ) )
        = ( k3_tarski @ X12 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X12 ) @ X12 ) ) ),
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
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('9',plain,(
    ! [X10: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k9_setfam_1 @ X11 )
      = ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k9_setfam_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fcJRTm5Nd0
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:43:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 18 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.21/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.46  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.46  thf(t19_yellow_1, conjecture,
% 0.21/0.46    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.21/0.46  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t99_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.46  thf('1', plain, (![X10 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X10)) = (X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.46  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.46  thf('2', plain, (![X11 : $i]: ((k9_setfam_1 @ X11) = (k1_zfmisc_1 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('3', plain, (![X10 : $i]: ((k3_tarski @ (k9_setfam_1 @ X10)) = (X10))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(t14_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.21/0.46         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X12 : $i]:
% 0.21/0.46         (~ (r2_hidden @ (k3_tarski @ X12) @ X12)
% 0.21/0.46          | ((k4_yellow_0 @ (k2_yellow_1 @ X12)) = (k3_tarski @ X12))
% 0.21/0.46          | (v1_xboole_0 @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.21/0.46  thf(t7_boole, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]: (~ (r2_hidden @ X3 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_boole])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X12 : $i]:
% 0.21/0.46         (((k4_yellow_0 @ (k2_yellow_1 @ X12)) = (k3_tarski @ X12))
% 0.21/0.46          | ~ (r2_hidden @ (k3_tarski @ X12) @ X12))),
% 0.21/0.46      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.21/0.46              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.46  thf(t4_yellow_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k2_yellow_1 @ (k9_setfam_1 @ X13)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.46  thf('9', plain, (![X10 : $i]: ((k3_tarski @ (k9_setfam_1 @ X10)) = (X10))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.46  thf(d10_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.46  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.46  thf(d1_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X5 @ X6)
% 0.21/0.46          | (r2_hidden @ X5 @ X7)
% 0.21/0.46          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]:
% 0.21/0.46         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.46      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.46  thf('15', plain, (![X11 : $i]: ((k9_setfam_1 @ X11) = (k1_zfmisc_1 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]:
% 0.21/0.46         ((r2_hidden @ X5 @ (k9_setfam_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.46  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '16'])).
% 0.21/0.46  thf('18', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['10', '17'])).
% 0.21/0.46  thf('19', plain, (((sk_A) != (sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '18'])).
% 0.21/0.46  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
