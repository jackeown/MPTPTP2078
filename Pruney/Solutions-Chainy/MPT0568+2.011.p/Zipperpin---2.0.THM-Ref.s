%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.csvPSL227i

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:49 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  196 ( 288 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('3',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['5','11'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','10'])).

thf('21',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['12','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.csvPSL227i
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:37:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 545 iterations in 0.261s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.50/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.50/0.71  thf(l13_xboole_0, axiom,
% 0.50/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.50/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.50/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.71      inference('sup+', [status(thm)], ['0', '1'])).
% 0.50/0.71  thf(t172_relat_1, conjecture,
% 0.50/0.71    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.50/0.71  thf('3', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (((X0) != (k1_xboole_0))
% 0.50/0.71          | ~ (v1_xboole_0 @ X0)
% 0.50/0.71          | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      ((~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))
% 0.50/0.71        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['4'])).
% 0.50/0.71  thf(d1_xboole_0, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.50/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.71  thf(t113_zfmisc_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.50/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      (![X5 : $i, X6 : $i]:
% 0.50/0.71         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['7'])).
% 0.50/0.71  thf(t152_zfmisc_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.50/0.71      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.50/0.71  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.50/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.71  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.71      inference('sup-', [status(thm)], ['6', '10'])).
% 0.50/0.71  thf('12', plain, (~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.50/0.71      inference('simplify_reflect+', [status(thm)], ['5', '11'])).
% 0.50/0.71  thf(cc1_relat_1, axiom,
% 0.50/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.50/0.71  thf('13', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.50/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.71  thf(t166_relat_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( v1_relat_1 @ C ) =>
% 0.50/0.71       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.50/0.71         ( ?[D:$i]:
% 0.50/0.71           ( ( r2_hidden @ D @ B ) & 
% 0.50/0.71             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.50/0.71             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.50/0.71  thf('15', plain,
% 0.50/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.50/0.71          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D @ X13 @ X11 @ X12)) @ X13)
% 0.50/0.71          | ~ (v1_relat_1 @ X13))),
% 0.50/0.71      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((v1_xboole_0 @ (k10_relat_1 @ X1 @ X0))
% 0.50/0.71          | ~ (v1_relat_1 @ X1)
% 0.50/0.71          | (r2_hidden @ 
% 0.50/0.71             (k4_tarski @ (sk_B @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.50/0.71              (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.50/0.71             X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.71  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.50/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.71          | (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.71          | (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['13', '18'])).
% 0.50/0.71  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.71      inference('sup-', [status(thm)], ['6', '10'])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X0 : $i]: (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['19', '20'])).
% 0.50/0.71  thf('22', plain, ($false), inference('demod', [status(thm)], ['12', '21'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
