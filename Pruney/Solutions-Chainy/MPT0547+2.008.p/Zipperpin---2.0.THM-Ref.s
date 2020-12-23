%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KJswdEABsU

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 175 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(fc16_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc16_relat_1])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
        = ( k9_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

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

thf('12',plain,(
    ( k9_relat_1 @ sk_A_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KJswdEABsU
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 54 iterations in 0.041s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(fc16_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_xboole_0 @ B ) ) =>
% 0.20/0.48       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.20/0.48         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X4)
% 0.20/0.48          | ~ (v1_xboole_0 @ X5)
% 0.20/0.48          | (v1_xboole_0 @ (k7_relat_1 @ X4 @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc16_relat_1])).
% 0.20/0.48  thf(t6_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t6_boole])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t148_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 0.20/0.48          | ~ (v1_relat_1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.48  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.48  thf(fc11_relat_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t6_boole])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k1_xboole_0) = (k9_relat_1 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ((k1_xboole_0) = (k9_relat_1 @ X1 @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.48  thf(t149_relat_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ A ) =>
% 0.20/0.48          ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t149_relat_1])).
% 0.20/0.48  thf('12', plain, (((k9_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_A_1)
% 0.20/0.48        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain, ((v1_relat_1 @ sk_A_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.48  thf('16', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.48  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
