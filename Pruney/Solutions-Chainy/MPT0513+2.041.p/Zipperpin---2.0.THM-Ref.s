%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HzE2AhzF7A

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:30 EST 2020

% Result     : Theorem 0.10s
% Output     : Refutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   40 (  62 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  180 ( 323 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('3',plain,
    ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X11 ) @ X12 )
        = ( k7_relat_1 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = ( k7_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','9'])).

thf('16',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','8'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HzE2AhzF7A
% 0.06/0.25  % Computer   : n013.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 14:18:54 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running portfolio for 600 s
% 0.06/0.25  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.06/0.25  % Number of cores: 8
% 0.06/0.26  % Python version: Python 3.6.8
% 0.06/0.26  % Running in FO mode
% 0.10/0.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.10/0.32  % Solved by: fo/fo7.sh
% 0.10/0.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.10/0.32  % done 18 iterations in 0.007s
% 0.10/0.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.10/0.32  % SZS output start Refutation
% 0.10/0.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.10/0.32  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.10/0.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.10/0.32  thf(sk_B_type, type, sk_B: $i > $i).
% 0.10/0.32  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.10/0.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.10/0.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.10/0.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.10/0.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.10/0.32  thf(sk_A_type, type, sk_A: $i).
% 0.10/0.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.10/0.32  thf(t111_relat_1, conjecture,
% 0.10/0.32    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.10/0.32  thf(zf_stmt_0, negated_conjecture,
% 0.10/0.32    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.10/0.32    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.10/0.32  thf('0', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.10/0.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.32  thf(t60_relat_1, axiom,
% 0.10/0.32    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.10/0.32     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.10/0.32  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.10/0.32      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.10/0.32  thf(t98_relat_1, axiom,
% 0.10/0.32    (![A:$i]:
% 0.10/0.32     ( ( v1_relat_1 @ A ) =>
% 0.10/0.32       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.10/0.32  thf('2', plain,
% 0.10/0.32      (![X14 : $i]:
% 0.10/0.32         (((k7_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (X14))
% 0.10/0.32          | ~ (v1_relat_1 @ X14))),
% 0.10/0.32      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.10/0.32  thf('3', plain,
% 0.10/0.32      ((((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.10/0.32        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.10/0.32      inference('sup+', [status(thm)], ['1', '2'])).
% 0.10/0.32  thf(d1_relat_1, axiom,
% 0.10/0.32    (![A:$i]:
% 0.10/0.32     ( ( v1_relat_1 @ A ) <=>
% 0.10/0.32       ( ![B:$i]:
% 0.10/0.32         ( ~( ( r2_hidden @ B @ A ) & 
% 0.10/0.32              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.10/0.32  thf('4', plain,
% 0.10/0.32      (![X8 : $i]: ((v1_relat_1 @ X8) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.10/0.32      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.10/0.32  thf(t113_zfmisc_1, axiom,
% 0.10/0.32    (![A:$i,B:$i]:
% 0.10/0.32     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.10/0.32       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.10/0.32  thf('5', plain,
% 0.10/0.32      (![X2 : $i, X3 : $i]:
% 0.10/0.32         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.10/0.32      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.10/0.32  thf('6', plain,
% 0.10/0.32      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.10/0.32      inference('simplify', [status(thm)], ['5'])).
% 0.10/0.32  thf(t152_zfmisc_1, axiom,
% 0.10/0.32    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.10/0.32  thf('7', plain,
% 0.10/0.32      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.10/0.32      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.10/0.32  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.10/0.32      inference('sup-', [status(thm)], ['6', '7'])).
% 0.10/0.32  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.10/0.32      inference('sup-', [status(thm)], ['4', '8'])).
% 0.10/0.32  thf('10', plain,
% 0.10/0.32      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.10/0.32      inference('demod', [status(thm)], ['3', '9'])).
% 0.10/0.32  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.10/0.32  thf('11', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.10/0.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.10/0.32  thf(t102_relat_1, axiom,
% 0.10/0.32    (![A:$i,B:$i,C:$i]:
% 0.10/0.32     ( ( v1_relat_1 @ C ) =>
% 0.10/0.32       ( ( r1_tarski @ A @ B ) =>
% 0.10/0.32         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.10/0.32  thf('12', plain,
% 0.10/0.32      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.10/0.32         (~ (r1_tarski @ X11 @ X12)
% 0.10/0.32          | ~ (v1_relat_1 @ X13)
% 0.10/0.32          | ((k7_relat_1 @ (k7_relat_1 @ X13 @ X11) @ X12)
% 0.10/0.32              = (k7_relat_1 @ X13 @ X11)))),
% 0.10/0.32      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.10/0.32  thf('13', plain,
% 0.10/0.32      (![X0 : $i, X1 : $i]:
% 0.10/0.32         (((k7_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0) @ X0)
% 0.10/0.32            = (k7_relat_1 @ X1 @ k1_xboole_0))
% 0.10/0.32          | ~ (v1_relat_1 @ X1))),
% 0.10/0.32      inference('sup-', [status(thm)], ['11', '12'])).
% 0.10/0.32  thf('14', plain,
% 0.10/0.32      (![X0 : $i]:
% 0.10/0.32         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 0.10/0.32            = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.10/0.32          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.10/0.32      inference('sup+', [status(thm)], ['10', '13'])).
% 0.10/0.32  thf('15', plain,
% 0.10/0.32      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.10/0.32      inference('demod', [status(thm)], ['3', '9'])).
% 0.10/0.32  thf('16', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.10/0.32      inference('sup-', [status(thm)], ['4', '8'])).
% 0.10/0.32  thf('17', plain,
% 0.10/0.32      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.10/0.32      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.10/0.32  thf('18', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.10/0.32      inference('demod', [status(thm)], ['0', '17'])).
% 0.10/0.32  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.10/0.32  
% 0.10/0.32  % SZS output end Refutation
% 0.10/0.32  
% 0.10/0.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
