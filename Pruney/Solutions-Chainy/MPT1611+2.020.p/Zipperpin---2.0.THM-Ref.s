%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o8nfsEAwzf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 211 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X7: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X7 ) )
      = X7 ) ),
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
    ! [X7: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X7 ) )
      = X7 ) ),
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

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k3_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( k9_setfam_1 @ X11 )
      = ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('8',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ ( k9_setfam_1 @ ( k3_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_tarski @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k3_yellow_1 @ X14 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['5','12','13','14'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    ! [X11: $i] :
      ( ( k9_setfam_1 @ X11 )
      = ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('18',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['15','18'])).

thf('20',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o8nfsEAwzf
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 20 iterations in 0.012s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(t19_yellow_1, conjecture,
% 0.21/0.46    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.21/0.46  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t99_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.46  thf('1', plain, (![X7 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X7)) = (X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.46  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.46  thf('2', plain, (![X11 : $i]: ((k9_setfam_1 @ X11) = (k1_zfmisc_1 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('3', plain, (![X7 : $i]: ((k3_tarski @ (k9_setfam_1 @ X7)) = (X7))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(t14_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.21/0.46         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X13 : $i]:
% 0.21/0.46         (~ (r2_hidden @ (k3_tarski @ X13) @ X13)
% 0.21/0.46          | ((k4_yellow_0 @ (k2_yellow_1 @ X13)) = (k3_tarski @ X13))
% 0.21/0.46          | (v1_xboole_0 @ X13))),
% 0.21/0.46      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.21/0.46              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf(t100_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X2 : $i]: (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k3_tarski @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.21/0.46  thf('7', plain, (![X11 : $i]: ((k9_setfam_1 @ X11) = (k1_zfmisc_1 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X2 : $i]: (r1_tarski @ X2 @ (k9_setfam_1 @ (k3_tarski @ X2)))),
% 0.21/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf(t37_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         ((r2_hidden @ X4 @ X5) | ~ (r1_tarski @ (k1_tarski @ X4) @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (r2_hidden @ X0 @ (k9_setfam_1 @ (k3_tarski @ (k1_tarski @ X0))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf(t31_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.46  thf('11', plain, (![X3 : $i]: ((k3_tarski @ (k1_tarski @ X3)) = (X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.21/0.46  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf(t4_yellow_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X14 : $i]: ((k3_yellow_1 @ X14) = (k2_yellow_1 @ (k9_setfam_1 @ X14)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.46  thf('14', plain, (![X7 : $i]: ((k3_tarski @ (k9_setfam_1 @ X7)) = (X7))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['5', '12', '13', '14'])).
% 0.21/0.46  thf(fc1_subset_1, axiom,
% 0.21/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.46  thf('16', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.46  thf('17', plain, (![X11 : $i]: ((k9_setfam_1 @ X11) = (k1_zfmisc_1 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('18', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X8))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.21/0.46      inference('clc', [status(thm)], ['15', '18'])).
% 0.21/0.46  thf('20', plain, (((sk_A) != (sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '19'])).
% 0.21/0.46  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
