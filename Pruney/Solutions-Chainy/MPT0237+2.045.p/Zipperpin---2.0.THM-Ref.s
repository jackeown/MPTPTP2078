%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hVw4uMQ54R

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:04 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   41 (  67 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  262 ( 516 expanded)
%              Number of equality atoms :   38 (  71 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X49: $i,X51: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X49 ) @ X51 )
        = ( k1_tarski @ X49 ) )
      | ( r2_hidden @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X54 ) @ ( k1_tarski @ X55 ) )
        = ( k2_tarski @ X54 @ X55 ) )
      | ( X54 = X55 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','9'])).

thf('11',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('15',plain,(
    ! [X56: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X56 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf('20',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','18','19','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hVw4uMQ54R
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 437 iterations in 0.162s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(t32_zfmisc_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.46/0.66       ( k2_tarski @ A @ B ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i]:
% 0.46/0.66        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.46/0.66          ( k2_tarski @ A @ B ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.46/0.66         != (k2_tarski @ sk_A @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(l51_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X52 : $i, X53 : $i]:
% 0.46/0.66         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.46/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.46/0.66         != (k2_tarski @ sk_A @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf(l33_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.66       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X49 : $i, X51 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ (k1_tarski @ X49) @ X51) = (k1_tarski @ X49))
% 0.46/0.66          | (r2_hidden @ X49 @ X51))),
% 0.46/0.66      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.46/0.66  thf(t98_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X7 @ X8)
% 0.46/0.66           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.46/0.66            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.46/0.66          | (r2_hidden @ X0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['3', '4'])).
% 0.46/0.66  thf(t29_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) != ( B ) ) =>
% 0.46/0.66       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.66         ( k2_tarski @ A @ B ) ) ))).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X54 : $i, X55 : $i]:
% 0.46/0.66         (((k5_xboole_0 @ (k1_tarski @ X54) @ (k1_tarski @ X55))
% 0.46/0.66            = (k2_tarski @ X54 @ X55))
% 0.46/0.66          | ((X54) = (X55)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.46/0.66            = (k2_tarski @ X1 @ X0))
% 0.46/0.66          | (r2_hidden @ X0 @ (k1_tarski @ X1))
% 0.46/0.66          | ((X1) = (X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.66  thf(d1_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X24 @ X23)
% 0.46/0.66          | ((X24) = (X21))
% 0.46/0.66          | ((X23) != (k1_tarski @ X21)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X21 : $i, X24 : $i]:
% 0.46/0.66         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X1) = (X0))
% 0.46/0.66          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.46/0.66              = (k2_tarski @ X1 @ X0)))),
% 0.46/0.66      inference('clc', [status(thm)], ['7', '9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.46/0.66         != (k2_tarski @ sk_A @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.46/0.66        | ((sk_A) = (sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('13', plain, (((sk_A) = (sk_B))),
% 0.46/0.66      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.66  thf(t69_enumset1, axiom,
% 0.46/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf(t31_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.46/0.66  thf('15', plain, (![X56 : $i]: ((k3_tarski @ (k1_tarski @ X56)) = (X56))),
% 0.46/0.66      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.46/0.66  thf('16', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X52 : $i, X53 : $i]:
% 0.46/0.66         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.46/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.66  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.66  thf('19', plain, (((sk_A) = (sk_B))),
% 0.46/0.66      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('21', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '13', '18', '19', '20'])).
% 0.46/0.66  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.51/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
