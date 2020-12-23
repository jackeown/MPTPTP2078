%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hmxN6vVT9T

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  55 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  234 ( 259 expanded)
%              Number of equality atoms :   30 (  35 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X43: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X46: $i] :
      ( ( k9_setfam_1 @ X46 )
      = ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X43: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X43 ) )
      = X43 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X48: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X48 ) @ X48 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X48 ) )
        = ( k3_tarski @ X48 ) )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ X41 @ ( k1_tarski @ X40 ) )
       != X41 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X48: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X48 ) )
        = ( k3_tarski @ X48 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X48 ) @ X48 ) ) ),
    inference(clc,[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X49: $i] :
      ( ( k3_yellow_1 @ X49 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('14',plain,(
    ! [X43: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X43 ) )
      = X43 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X37 )
      | ( X37
       != ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X46: $i] :
      ( ( k9_setfam_1 @ X46 )
      = ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ ( k9_setfam_1 @ X36 ) )
      | ~ ( r1_tarski @ X35 @ X36 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hmxN6vVT9T
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 46 iterations in 0.046s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.50  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(t19_yellow_1, conjecture,
% 0.20/0.50    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.20/0.50  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t99_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.50  thf('1', plain, (![X43 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X43)) = (X43))),
% 0.20/0.50      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.50  thf(redefinition_k9_setfam_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.50  thf('2', plain, (![X46 : $i]: ((k9_setfam_1 @ X46) = (k1_zfmisc_1 @ X46))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.50  thf('3', plain, (![X43 : $i]: ((k3_tarski @ (k9_setfam_1 @ X43)) = (X43))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(t14_yellow_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.20/0.50         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X48 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (k3_tarski @ X48) @ X48)
% 0.20/0.50          | ((k4_yellow_0 @ (k2_yellow_1 @ X48)) = (k3_tarski @ X48))
% 0.20/0.50          | (v1_xboole_0 @ X48))),
% 0.20/0.50      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.20/0.50  thf(l13_xboole_0, axiom,
% 0.20/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.50  thf(t4_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.50  thf(t65_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X40 : $i, X41 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X40 @ X41)
% 0.20/0.50          | ((k4_xboole_0 @ X41 @ (k1_tarski @ X40)) != (X41)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X48 : $i]:
% 0.20/0.50         (((k4_yellow_0 @ (k2_yellow_1 @ X48)) = (k3_tarski @ X48))
% 0.20/0.50          | ~ (r2_hidden @ (k3_tarski @ X48) @ X48))),
% 0.20/0.50      inference('clc', [status(thm)], ['4', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.20/0.50          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.20/0.50              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '11'])).
% 0.20/0.50  thf(t4_yellow_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X49 : $i]: ((k3_yellow_1 @ X49) = (k2_yellow_1 @ (k9_setfam_1 @ X49)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.50  thf('14', plain, (![X43 : $i]: ((k3_tarski @ (k9_setfam_1 @ X43)) = (X43))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.20/0.50          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('17', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.50  thf(d1_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X35 @ X36)
% 0.20/0.50          | (r2_hidden @ X35 @ X37)
% 0.20/0.50          | ((X37) != (k1_zfmisc_1 @ X36)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i]:
% 0.20/0.50         ((r2_hidden @ X35 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X35 @ X36))),
% 0.20/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.50  thf('20', plain, (![X46 : $i]: ((k9_setfam_1 @ X46) = (k1_zfmisc_1 @ X46))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i]:
% 0.20/0.50         ((r2_hidden @ X35 @ (k9_setfam_1 @ X36)) | ~ (r1_tarski @ X35 @ X36))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '21'])).
% 0.20/0.50  thf('23', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '22'])).
% 0.20/0.50  thf('24', plain, (((sk_A) != (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '23'])).
% 0.20/0.50  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
