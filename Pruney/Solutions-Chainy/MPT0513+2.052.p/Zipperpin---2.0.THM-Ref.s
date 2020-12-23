%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ObOr0NIUuN

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 138 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( ( k7_relat_1 @ X5 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( ( ( k7_relat_1 @ X5 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X4 @ X2 ) @ X3 )
        = ( k7_relat_1 @ X4 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = ( k7_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X1 )
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X1 )
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('10',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ObOr0NIUuN
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:48:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 12 iterations in 0.017s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.19/0.51  thf('0', plain, (![X1 : $i]: (v1_relat_1 @ (k6_relat_1 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.51  thf(t110_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (![X5 : $i]:
% 0.19/0.51         (((k7_relat_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X5))),
% 0.19/0.51      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X5 : $i]:
% 0.19/0.51         (((k7_relat_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X5))),
% 0.19/0.51      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.19/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.51  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.51  thf(t102_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ C ) =>
% 0.19/0.51       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.51         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.51         (~ (r1_tarski @ X2 @ X3)
% 0.19/0.51          | ~ (v1_relat_1 @ X4)
% 0.19/0.51          | ((k7_relat_1 @ (k7_relat_1 @ X4 @ X2) @ X3)
% 0.19/0.51              = (k7_relat_1 @ X4 @ X2)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k7_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0) @ X0)
% 0.19/0.51            = (k7_relat_1 @ X1 @ k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k7_relat_1 @ k1_xboole_0 @ X1) = (k7_relat_1 @ X0 @ k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['2', '5'])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k7_relat_1 @ k1_xboole_0 @ X1) = (k7_relat_1 @ X0 @ k1_xboole_0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X1)
% 0.19/0.51          | ~ (v1_relat_1 @ X1))),
% 0.19/0.51      inference('sup+', [status(thm)], ['1', '7'])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X1)
% 0.19/0.51          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.51  thf(t111_relat_1, conjecture,
% 0.19/0.51    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.19/0.51  thf('10', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf('12', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.19/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.51  thf('13', plain, ($false), inference('sup-', [status(thm)], ['0', '12'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
