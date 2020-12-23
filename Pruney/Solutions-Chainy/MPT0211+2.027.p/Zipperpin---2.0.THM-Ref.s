%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qKMfrsI0xx

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:33 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 132 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  436 (1316 expanded)
%              Number of equality atoms :   41 ( 123 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X26 @ X29 @ X28 @ X27 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X83: $i,X84: $i,X85: $i] :
      ( ( k2_enumset1 @ X83 @ X83 @ X84 @ X85 )
      = ( k1_enumset1 @ X83 @ X84 @ X85 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l129_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ A @ D ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X14 @ X13 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l129_enumset1])).

thf('7',plain,(
    ! [X83: $i,X84: $i,X85: $i] :
      ( ( k2_enumset1 @ X83 @ X83 @ X84 @ X85 )
      = ( k1_enumset1 @ X83 @ X84 @ X85 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('10',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X60 @ X61 @ X62 ) @ ( k1_tarski @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X60 @ X61 @ X62 ) @ ( k1_tarski @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','15'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X33 @ X30 @ X32 @ X31 )
      = ( k2_enumset1 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('18',plain,(
    ! [X83: $i,X84: $i,X85: $i] :
      ( ( k2_enumset1 @ X83 @ X83 @ X84 @ X85 )
      = ( k1_enumset1 @ X83 @ X84 @ X85 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('21',plain,(
    ( k1_enumset1 @ sk_C @ sk_A @ sk_B )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X26 @ X29 @ X28 @ X27 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X37 @ X36 @ X35 @ X34 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('26',plain,(
    ! [X83: $i,X84: $i,X85: $i] :
      ( ( k2_enumset1 @ X83 @ X83 @ X84 @ X85 )
      = ( k1_enumset1 @ X83 @ X84 @ X85 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('31',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','28','29','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qKMfrsI0xx
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.68  % Solved by: fo/fo7.sh
% 0.44/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.68  % done 145 iterations in 0.198s
% 0.44/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.68  % SZS output start Refutation
% 0.44/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.44/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(t137_enumset1, conjecture,
% 0.44/0.68    (![A:$i,B:$i,C:$i]:
% 0.44/0.68     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.44/0.68       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.44/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.68        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.44/0.68          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.44/0.68    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.44/0.68  thf('0', plain,
% 0.44/0.68      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.44/0.68         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(l53_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.44/0.68       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.44/0.68  thf('1', plain,
% 0.44/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.44/0.68           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k2_tarski @ X19 @ X20)))),
% 0.44/0.68      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.44/0.68  thf('2', plain,
% 0.44/0.68      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.44/0.68         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.44/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.68  thf(t107_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.44/0.68  thf('3', plain,
% 0.44/0.68      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X26 @ X29 @ X28 @ X27)
% 0.44/0.68           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.44/0.68      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.44/0.68  thf(t71_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i]:
% 0.44/0.68     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.44/0.68  thf('4', plain,
% 0.44/0.68      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X83 @ X83 @ X84 @ X85)
% 0.44/0.68           = (k1_enumset1 @ X83 @ X84 @ X85))),
% 0.44/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.68  thf('5', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.44/0.68      inference('sup+', [status(thm)], ['3', '4'])).
% 0.44/0.68  thf(l129_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.44/0.68  thf('6', plain,
% 0.44/0.68      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X15 @ X14 @ X13 @ X16)
% 0.44/0.68           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.44/0.68      inference('cnf', [status(esa)], [l129_enumset1])).
% 0.44/0.68  thf('7', plain,
% 0.44/0.68      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X83 @ X83 @ X84 @ X85)
% 0.44/0.68           = (k1_enumset1 @ X83 @ X84 @ X85))),
% 0.44/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.68  thf('8', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.68  thf('9', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.44/0.68      inference('sup+', [status(thm)], ['5', '8'])).
% 0.44/0.68  thf(t46_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.44/0.68       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.44/0.68  thf('10', plain,
% 0.44/0.68      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X60 @ X61 @ X62 @ X63)
% 0.44/0.68           = (k2_xboole_0 @ (k1_enumset1 @ X60 @ X61 @ X62) @ (k1_tarski @ X63)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.44/0.68  thf('11', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2)
% 0.44/0.68           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['9', '10'])).
% 0.44/0.68  thf('12', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.68  thf('13', plain,
% 0.44/0.68      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X60 @ X61 @ X62 @ X63)
% 0.44/0.68           = (k2_xboole_0 @ (k1_enumset1 @ X60 @ X61 @ X62) @ (k1_tarski @ X63)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.44/0.68  thf('14', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.68  thf('15', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.44/0.68      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.44/0.68  thf('16', plain,
% 0.44/0.68      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.44/0.68         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.44/0.68      inference('demod', [status(thm)], ['2', '15'])).
% 0.44/0.68  thf(t113_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 0.44/0.68  thf('17', plain,
% 0.44/0.68      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X33 @ X30 @ X32 @ X31)
% 0.44/0.68           = (k2_enumset1 @ X30 @ X31 @ X32 @ X33))),
% 0.44/0.68      inference('cnf', [status(esa)], [t113_enumset1])).
% 0.44/0.68  thf('18', plain,
% 0.44/0.68      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X83 @ X83 @ X84 @ X85)
% 0.44/0.68           = (k1_enumset1 @ X83 @ X84 @ X85))),
% 0.44/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.68  thf('19', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.44/0.68      inference('sup+', [status(thm)], ['17', '18'])).
% 0.44/0.68  thf('20', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.44/0.68      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.44/0.68  thf('21', plain,
% 0.44/0.68      (((k1_enumset1 @ sk_C @ sk_A @ sk_B)
% 0.44/0.68         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.44/0.68      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.44/0.68  thf('22', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.68  thf('23', plain,
% 0.44/0.68      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X26 @ X29 @ X28 @ X27)
% 0.44/0.68           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.44/0.68      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.44/0.68  thf('24', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X1 @ X0 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.44/0.68  thf(t125_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.44/0.68  thf('25', plain,
% 0.44/0.68      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X37 @ X36 @ X35 @ X34)
% 0.44/0.68           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 0.44/0.68      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.44/0.68  thf('26', plain,
% 0.44/0.68      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X83 @ X83 @ X84 @ X85)
% 0.44/0.68           = (k1_enumset1 @ X83 @ X84 @ X85))),
% 0.44/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.68  thf('27', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.44/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.44/0.68  thf('28', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.44/0.68      inference('sup+', [status(thm)], ['24', '27'])).
% 0.44/0.68  thf('29', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.44/0.68      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.44/0.68  thf('30', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.44/0.68      inference('sup+', [status(thm)], ['24', '27'])).
% 0.44/0.68  thf('31', plain,
% 0.44/0.68      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.44/0.68         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['21', '28', '29', '30'])).
% 0.44/0.68  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.44/0.68  
% 0.44/0.68  % SZS output end Refutation
% 0.44/0.68  
% 0.44/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
