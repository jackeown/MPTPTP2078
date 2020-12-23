%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rN9MnM4ghW

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  291 ( 350 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_wellord1 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X5 ) @ ( k3_xboole_0 @ X4 @ X6 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_wellord1 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_wellord1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_wellord1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_wellord1 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_wellord1 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['9','13'])).

thf(t26_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
          = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_wellord1])).

thf('15',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
     != ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rN9MnM4ghW
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 42 iterations in 0.060s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(d6_wellord1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( k2_wellord1 @ A @ B ) =
% 0.21/0.53           ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (((k2_wellord1 @ X11 @ X12)
% 0.21/0.53            = (k3_xboole_0 @ X11 @ (k2_zfmisc_1 @ X12 @ X12)))
% 0.21/0.53          | ~ (v1_relat_1 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.21/0.53  thf(t16_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.53       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ (k2_wellord1 @ X1 @ X0) @ X2)
% 0.21/0.53            = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0) @ X2)))
% 0.21/0.53          | ~ (v1_relat_1 @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf(t123_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.21/0.53       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X5) @ (k3_xboole_0 @ X4 @ X6))
% 0.21/0.53           = (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X4) @ (k2_zfmisc_1 @ X5 @ X6)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (((k2_wellord1 @ X11 @ X12)
% 0.21/0.53            = (k3_xboole_0 @ X11 @ (k2_zfmisc_1 @ X12 @ X12)))
% 0.21/0.53          | ~ (v1_relat_1 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.53            = (k3_xboole_0 @ X2 @ 
% 0.21/0.53               (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X1) @ (k2_zfmisc_1 @ X0 @ X0))))
% 0.21/0.53          | ~ (v1_relat_1 @ X2))),
% 0.21/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.53            = (k3_xboole_0 @ (k2_wellord1 @ X2 @ X1) @ (k2_zfmisc_1 @ X0 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X2)
% 0.21/0.53          | ~ (v1_relat_1 @ X2))),
% 0.21/0.53      inference('sup+', [status(thm)], ['2', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X2)
% 0.21/0.53          | ((k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.53              = (k3_xboole_0 @ (k2_wellord1 @ X2 @ X1) @ 
% 0.21/0.53                 (k2_zfmisc_1 @ X0 @ X0))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (((k2_wellord1 @ X11 @ X12)
% 0.21/0.53            = (k3_xboole_0 @ X11 @ (k2_zfmisc_1 @ X12 @ X12)))
% 0.21/0.53          | ~ (v1_relat_1 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.21/0.53            = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X2)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_wellord1 @ X2 @ X1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (((k2_wellord1 @ X11 @ X12)
% 0.21/0.53            = (k3_xboole_0 @ X11 @ (k2_zfmisc_1 @ X12 @ X12)))
% 0.21/0.53          | ~ (v1_relat_1 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.21/0.53  thf(fc1_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k2_wellord1 @ X1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X2)
% 0.21/0.53          | ((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.21/0.53              = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.21/0.53      inference('clc', [status(thm)], ['9', '13'])).
% 0.21/0.53  thf(t26_wellord1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.21/0.53         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( v1_relat_1 @ C ) =>
% 0.21/0.53          ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.21/0.53            ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t26_wellord1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.53         != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.53          != (k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.53         != (k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
