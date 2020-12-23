%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZKqJuimqdm

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   91 (  91 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(fc17_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc17_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(clc,[status(thm)],['0','1'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('5',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZKqJuimqdm
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 32 iterations in 0.014s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.47  thf(fc17_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.19/0.47       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.19/0.47         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ X4)
% 0.19/0.47          | ~ (v1_xboole_0 @ X4)
% 0.19/0.47          | (v1_xboole_0 @ (k7_relat_1 @ X4 @ X5)))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc17_relat_1])).
% 0.19/0.47  thf(cc1_relat_1, axiom,
% 0.19/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.19/0.47  thf('1', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ (k7_relat_1 @ X4 @ X5)) | ~ (v1_xboole_0 @ X4))),
% 0.19/0.47      inference('clc', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf(l13_xboole_0, axiom,
% 0.19/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (v1_xboole_0 @ X1) | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf(t111_relat_1, conjecture,
% 0.19/0.47    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.19/0.47  thf('5', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('7', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.47  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 0.19/0.47  thf('8', plain, (![X2 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc13_subset_1])).
% 0.19/0.47  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.47  thf('10', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '9'])).
% 0.19/0.47  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
