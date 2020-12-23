%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nRMlrCcxeA

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  45 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  180 ( 190 expanded)
%              Number of equality atoms :   27 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('0',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X35 @ X36 )
        = ( k3_xboole_0 @ X35 @ ( k2_zfmisc_1 @ X36 @ ( k2_relat_1 @ X35 ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X35 @ X36 )
        = ( k1_setfam_1 @ ( k2_tarski @ X35 @ ( k2_zfmisc_1 @ X36 @ ( k2_relat_1 @ X35 ) ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_zfmisc_1 @ X30 @ X31 )
        = k1_xboole_0 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X30: $i] :
      ( ( k2_zfmisc_1 @ X30 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('9',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('12',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X34: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','7','10','17'])).

thf('19',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nRMlrCcxeA
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 64 iterations in 0.042s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(t111_relat_1, conjecture,
% 0.21/0.50    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.21/0.50  thf('0', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t60_relat_1, axiom,
% 0.21/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf(t96_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( k7_relat_1 @ B @ A ) =
% 0.21/0.50         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X35 : $i, X36 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X35 @ X36)
% 0.21/0.50            = (k3_xboole_0 @ X35 @ (k2_zfmisc_1 @ X36 @ (k2_relat_1 @ X35))))
% 0.21/0.50          | ~ (v1_relat_1 @ X35))),
% 0.21/0.50      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.21/0.50  thf(t12_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X32 : $i, X33 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X35 : $i, X36 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X35 @ X36)
% 0.21/0.50            = (k1_setfam_1 @ 
% 0.21/0.50               (k2_tarski @ X35 @ (k2_zfmisc_1 @ X36 @ (k2_relat_1 @ X35)))))
% 0.21/0.50          | ~ (v1_relat_1 @ X35))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 0.21/0.50            = (k1_setfam_1 @ 
% 0.21/0.50               (k2_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))))
% 0.21/0.50          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf(t113_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X30 : $i, X31 : $i]:
% 0.21/0.50         (((k2_zfmisc_1 @ X30 @ X31) = (k1_xboole_0))
% 0.21/0.50          | ((X31) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X30 : $i]: ((k2_zfmisc_1 @ X30 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.50  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X32 : $i, X33 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.21/0.50  thf('11', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.21/0.50  thf('12', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.21/0.50  thf(l13_xboole_0, axiom,
% 0.21/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.50  thf('14', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.50  thf(cc1_relat_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.50  thf('16', plain, (![X34 : $i]: ((v1_relat_1 @ X34) | ~ (v1_xboole_0 @ X34))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.50  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '7', '10', '17'])).
% 0.21/0.50  thf('19', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '18'])).
% 0.21/0.50  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
