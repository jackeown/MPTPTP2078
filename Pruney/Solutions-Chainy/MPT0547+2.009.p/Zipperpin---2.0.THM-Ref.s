%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UVe7bcka3g

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:02 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 116 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t149_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k9_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t149_relat_1])).

thf('6',plain,(
    ( k9_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UVe7bcka3g
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:55:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 6 iterations in 0.006s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.48  thf(t110_relat_1, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( v1_relat_1 @ A ) =>
% 0.23/0.48       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.23/0.48          | ~ (v1_relat_1 @ X0))),
% 0.23/0.48      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.23/0.48  thf(t148_relat_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( v1_relat_1 @ B ) =>
% 0.23/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (![X1 : $i, X2 : $i]:
% 0.23/0.48         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X2)) = (k9_relat_1 @ X1 @ X2))
% 0.23/0.48          | ~ (v1_relat_1 @ X1))),
% 0.23/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.23/0.48          | ~ (v1_relat_1 @ X0)
% 0.23/0.48          | ~ (v1_relat_1 @ X0))),
% 0.23/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.23/0.48  thf(t60_relat_1, axiom,
% 0.23/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.23/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.48  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.48  thf('4', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (((k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.23/0.48          | ~ (v1_relat_1 @ X0)
% 0.23/0.48          | ~ (v1_relat_1 @ X0))),
% 0.23/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.48  thf('5', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (~ (v1_relat_1 @ X0)
% 0.23/0.48          | ((k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.23/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.23/0.48  thf(t149_relat_1, conjecture,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( v1_relat_1 @ A ) =>
% 0.23/0.48       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i]:
% 0.23/0.48        ( ( v1_relat_1 @ A ) =>
% 0.23/0.48          ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t149_relat_1])).
% 0.23/0.48  thf('6', plain, (((k9_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('7', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.48  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('9', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.48  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
