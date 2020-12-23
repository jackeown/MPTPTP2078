%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7wG33VuxH1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  25 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 ( 101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t206_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v5_relat_1 @ k1_xboole_0 @ B )
        & ( v4_relat_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t206_relat_1])).

thf('0',plain,
    ( ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A )
   <= ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('3',plain,
    ( $false
   <= ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('5',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_B )
   <= ~ ( v5_relat_1 @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,(
    v5_relat_1 @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','7'])).

thf('9',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['3','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7wG33VuxH1
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 5 iterations in 0.005s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.47  thf(t206_relat_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t206_relat_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((~ (v4_relat_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.47        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((~ (v4_relat_1 @ k1_xboole_0 @ sk_A))
% 0.21/0.47         <= (~ ((v4_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(l222_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.47  thf('2', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.21/0.47      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.21/0.47  thf('3', plain, (($false) <= (~ ((v4_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.21/0.47      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((~ (v5_relat_1 @ k1_xboole_0 @ sk_B))
% 0.21/0.47         <= (~ ((v5_relat_1 @ k1_xboole_0 @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('6', plain, (((v5_relat_1 @ k1_xboole_0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (~ ((v4_relat_1 @ k1_xboole_0 @ sk_A)) | 
% 0.21/0.47       ~ ((v5_relat_1 @ k1_xboole_0 @ sk_B))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('8', plain, (~ ((v4_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, ($false), inference('simpl_trail', [status(thm)], ['3', '8'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
