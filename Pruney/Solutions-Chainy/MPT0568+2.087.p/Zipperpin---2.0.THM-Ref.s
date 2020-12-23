%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.txn951Zrf6

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 (  95 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  323 ( 460 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X43: $i] :
      ( ( ( k10_relat_1 @ X43 @ ( k2_relat_1 @ X43 ) )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('6',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X40: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('21',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k10_relat_1 @ X41 @ X42 )
        = ( k10_relat_1 @ X41 @ ( k3_xboole_0 @ ( k2_relat_1 @ X41 ) @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','17'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','34','35','36'])).

thf('38',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.txn951Zrf6
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:51:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 126 iterations in 0.084s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(t172_relat_1, conjecture,
% 0.22/0.54    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.22/0.54  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.54  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.54  thf(t8_boole, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t8_boole])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf(t60_relat_1, axiom,
% 0.22/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf(t169_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X43 : $i]:
% 0.22/0.54         (((k10_relat_1 @ X43 @ (k2_relat_1 @ X43)) = (k1_relat_1 @ X43))
% 0.22/0.54          | ~ (v1_relat_1 @ X43))),
% 0.22/0.54      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.22/0.54        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.54  thf(t71_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.54  thf('9', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.22/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.54  thf(fc8_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.22/0.54       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X40 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ (k1_relat_1 @ X40))
% 0.22/0.54          | ~ (v1_relat_1 @ X40)
% 0.22/0.54          | (v1_xboole_0 @ X40))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ X0)
% 0.22/0.54          | (v1_xboole_0 @ (k6_relat_1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.54  thf('12', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.54  thf('16', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '7', '18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['3', '19'])).
% 0.22/0.54  thf(t168_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( k10_relat_1 @ B @ A ) =
% 0.22/0.54         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X41 : $i, X42 : $i]:
% 0.22/0.54         (((k10_relat_1 @ X41 @ X42)
% 0.22/0.54            = (k10_relat_1 @ X41 @ (k3_xboole_0 @ (k2_relat_1 @ X41) @ X42)))
% 0.22/0.54          | ~ (v1_relat_1 @ X41))),
% 0.22/0.54      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('23', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf(t100_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.54  thf(t92_xboole_1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('25', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.55  thf('26', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.55  thf(t91_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.55       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.22/0.55           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.55           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['25', '28'])).
% 0.22/0.55  thf(t5_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.55  thf('30', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.55  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['24', '31'])).
% 0.22/0.55  thf(t4_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.55  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.55  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '17'])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['22', '23', '34', '35', '36'])).
% 0.22/0.55  thf('38', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['0', '37'])).
% 0.22/0.55  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
