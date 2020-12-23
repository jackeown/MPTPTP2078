%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9aW9UyQuuL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  168 ( 168 expanded)
%              Number of equality atoms :   31 (  31 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('13',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['12'])).

thf(t66_relat_1,conjecture,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t66_relat_1])).

thf('14',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9aW9UyQuuL
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 15 iterations in 0.011s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.47  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(t60_relat_1, axiom,
% 0.22/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.47  thf('0', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.47  thf(dt_k4_relat_1, axiom,
% 0.22/0.47    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.22/0.47  thf(t37_relat_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.22/0.47         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X6 : $i]:
% 0.22/0.47         (((k2_relat_1 @ X6) = (k1_relat_1 @ (k4_relat_1 @ X6)))
% 0.22/0.47          | ~ (v1_relat_1 @ X6))),
% 0.22/0.47      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.22/0.47  thf(t64_relat_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.47           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.47         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X7 : $i]:
% 0.22/0.47         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 0.22/0.47          | ((X7) = (k1_xboole_0))
% 0.22/0.47          | ~ (v1_relat_1 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.22/0.47          | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | ((k4_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.22/0.47          | ((k4_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.47          | ~ (v1_relat_1 @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.47        | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '6'])).
% 0.22/0.47  thf(t113_zfmisc_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i]:
% 0.22/0.47         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.47  thf(fc6_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.47  thf('11', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.47        | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.47      inference('demod', [status(thm)], ['7', '11'])).
% 0.22/0.47  thf('13', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.47  thf(t66_relat_1, conjecture,
% 0.22/0.47    (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (( k4_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t66_relat_1])).
% 0.22/0.47  thf('14', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('15', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
