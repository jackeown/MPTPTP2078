%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4wcZGPk7p8

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   81 (  91 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(cc4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v5_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v5_ordinal1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc4_ordinal1])).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('1',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('2',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('6',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('9',plain,(
    ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','4','7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4wcZGPk7p8
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:40:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 16 iterations in 0.010s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.47  thf(cc4_ordinal1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v5_ordinal1 @ A ) ))).
% 0.21/0.47  thf('0', plain, (![X4 : $i]: ((v5_ordinal1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc4_ordinal1])).
% 0.21/0.47  thf(t45_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.21/0.47       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.21/0.47          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.47  thf('2', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.47  thf(fc3_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('3', plain, (![X3 : $i]: (v1_funct_1 @ (k6_relat_1 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.47  thf('4', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.47  thf('6', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.47  thf('7', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf(l222_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.47  thf('8', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.21/0.47      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.21/0.47  thf('9', plain, (~ (v5_ordinal1 @ k1_xboole_0)),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '4', '7', '8'])).
% 0.21/0.47  thf('10', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '9'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('12', plain, ($false), inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
