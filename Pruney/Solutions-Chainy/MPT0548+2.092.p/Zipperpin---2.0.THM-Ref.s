%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RfLWtHfGWk

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 298 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('0',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k9_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ X8 @ ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = ( k9_relat_1 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','6','10'])).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('14',plain,
    ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('16',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('18',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('23',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RfLWtHfGWk
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:07:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 21 iterations in 0.020s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(t150_relat_1, conjecture,
% 0.21/0.46    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.21/0.46  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t60_relat_1, axiom,
% 0.21/0.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.46  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.46  thf(t145_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ( k9_relat_1 @ B @ A ) =
% 0.21/0.46         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i]:
% 0.21/0.46         (((k9_relat_1 @ X8 @ X9)
% 0.21/0.46            = (k9_relat_1 @ X8 @ (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9)))
% 0.21/0.46          | ~ (v1_relat_1 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k9_relat_1 @ k1_xboole_0 @ X0)
% 0.21/0.46            = (k9_relat_1 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 0.21/0.46          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(t48_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.46           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.46  thf(t4_boole, axiom,
% 0.21/0.46    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf(t113_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.46  thf(fc6_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.46  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.46      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k9_relat_1 @ k1_xboole_0 @ X0)
% 0.21/0.46           = (k9_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '6', '10'])).
% 0.21/0.46  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.46  thf(t98_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X12 : $i]:
% 0.21/0.46         (((k7_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (X12))
% 0.21/0.46          | ~ (v1_relat_1 @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      ((((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.46        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.46  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.46      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.46  thf(t148_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i]:
% 0.21/0.46         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.21/0.46          | ~ (v1_relat_1 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      ((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.46        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.46  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.46      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['11', '21'])).
% 0.21/0.46  thf('23', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '22'])).
% 0.21/0.46  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
