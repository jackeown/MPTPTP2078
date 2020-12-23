%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0HzBBqe8u9

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:08 EST 2020

% Result     : Theorem 4.65s
% Output     : Refutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :   59 (  70 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  559 ( 683 expanded)
%              Number of equality atoms :   46 (  57 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t108_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t108_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i] :
      ( ( k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82 )
      = ( k2_enumset1 @ X79 @ X80 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X76: $i,X77: $i,X78: $i] :
      ( ( k2_enumset1 @ X76 @ X76 @ X77 @ X78 )
      = ( k1_enumset1 @ X76 @ X77 @ X78 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('4',plain,(
    ! [X83: $i,X84: $i,X85: $i,X86: $i,X87: $i] :
      ( ( k4_enumset1 @ X83 @ X83 @ X84 @ X85 @ X86 @ X87 )
      = ( k3_enumset1 @ X83 @ X84 @ X85 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('7',plain,(
    ! [X88: $i,X89: $i,X90: $i,X91: $i,X92: $i,X93: $i] :
      ( ( k5_enumset1 @ X88 @ X88 @ X89 @ X90 @ X91 @ X92 @ X93 )
      = ( k4_enumset1 @ X88 @ X89 @ X90 @ X91 @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X83: $i,X84: $i,X85: $i,X86: $i,X87: $i] :
      ( ( k4_enumset1 @ X83 @ X83 @ X84 @ X85 @ X86 @ X87 )
      = ( k3_enumset1 @ X83 @ X84 @ X85 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X9 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('13',plain,(
    ! [X76: $i,X77: $i,X78: $i] :
      ( ( k2_enumset1 @ X76 @ X76 @ X77 @ X78 )
      = ( k1_enumset1 @ X76 @ X77 @ X78 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X76: $i,X77: $i,X78: $i] :
      ( ( k2_enumset1 @ X76 @ X76 @ X77 @ X78 )
      = ( k1_enumset1 @ X76 @ X77 @ X78 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X73: $i] :
      ( ( k2_tarski @ X73 @ X73 )
      = ( k1_tarski @ X73 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i] :
      ( ( k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82 )
      = ( k2_enumset1 @ X79 @ X80 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','24'])).

thf('26',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i] :
      ( ( k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82 )
      = ( k2_enumset1 @ X79 @ X80 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X9 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X9 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('33',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','27','30','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0HzBBqe8u9
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:45:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 4.65/4.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.65/4.83  % Solved by: fo/fo7.sh
% 4.65/4.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.65/4.83  % done 6959 iterations in 4.374s
% 4.65/4.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.65/4.83  % SZS output start Refutation
% 4.65/4.83  thf(sk_A_type, type, sk_A: $i).
% 4.65/4.83  thf(sk_C_type, type, sk_C: $i).
% 4.65/4.83  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.65/4.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.65/4.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.65/4.83  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 4.65/4.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.65/4.83  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 4.65/4.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.65/4.83  thf(sk_B_type, type, sk_B: $i).
% 4.65/4.83  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.65/4.83  thf(sk_D_type, type, sk_D: $i).
% 4.65/4.83  thf(t108_enumset1, conjecture,
% 4.65/4.83    (![A:$i,B:$i,C:$i,D:$i]:
% 4.65/4.83     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 4.65/4.83  thf(zf_stmt_0, negated_conjecture,
% 4.65/4.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.65/4.83        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 4.65/4.83    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 4.65/4.83  thf('0', plain,
% 4.65/4.83      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 4.65/4.83         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 4.65/4.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.65/4.83  thf(t72_enumset1, axiom,
% 4.65/4.83    (![A:$i,B:$i,C:$i,D:$i]:
% 4.65/4.83     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 4.65/4.83  thf('1', plain,
% 4.65/4.83      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i]:
% 4.65/4.83         ((k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82)
% 4.65/4.83           = (k2_enumset1 @ X79 @ X80 @ X81 @ X82))),
% 4.65/4.83      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.65/4.83  thf(t71_enumset1, axiom,
% 4.65/4.83    (![A:$i,B:$i,C:$i]:
% 4.65/4.83     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.65/4.83  thf('2', plain,
% 4.65/4.83      (![X76 : $i, X77 : $i, X78 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X76 @ X76 @ X77 @ X78)
% 4.65/4.83           = (k1_enumset1 @ X76 @ X77 @ X78))),
% 4.65/4.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.65/4.83  thf('3', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.65/4.83         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.65/4.83      inference('sup+', [status(thm)], ['1', '2'])).
% 4.65/4.83  thf(t73_enumset1, axiom,
% 4.65/4.83    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.65/4.83     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 4.65/4.83       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 4.65/4.83  thf('4', plain,
% 4.65/4.83      (![X83 : $i, X84 : $i, X85 : $i, X86 : $i, X87 : $i]:
% 4.65/4.83         ((k4_enumset1 @ X83 @ X83 @ X84 @ X85 @ X86 @ X87)
% 4.65/4.83           = (k3_enumset1 @ X83 @ X84 @ X85 @ X86 @ X87))),
% 4.65/4.83      inference('cnf', [status(esa)], [t73_enumset1])).
% 4.65/4.83  thf(t61_enumset1, axiom,
% 4.65/4.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 4.65/4.83     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 4.65/4.83       ( k2_xboole_0 @
% 4.65/4.83         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 4.65/4.83  thf('5', plain,
% 4.65/4.83      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 4.65/4.83         ((k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 4.65/4.83           = (k2_xboole_0 @ 
% 4.65/4.83              (k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31) @ 
% 4.65/4.83              (k1_tarski @ X32)))),
% 4.65/4.83      inference('cnf', [status(esa)], [t61_enumset1])).
% 4.65/4.83  thf('6', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.65/4.83         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 4.65/4.83           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 4.65/4.83              (k1_tarski @ X5)))),
% 4.65/4.83      inference('sup+', [status(thm)], ['4', '5'])).
% 4.65/4.83  thf(t74_enumset1, axiom,
% 4.65/4.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.65/4.83     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 4.65/4.83       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 4.65/4.83  thf('7', plain,
% 4.65/4.83      (![X88 : $i, X89 : $i, X90 : $i, X91 : $i, X92 : $i, X93 : $i]:
% 4.65/4.83         ((k5_enumset1 @ X88 @ X88 @ X89 @ X90 @ X91 @ X92 @ X93)
% 4.65/4.83           = (k4_enumset1 @ X88 @ X89 @ X90 @ X91 @ X92 @ X93))),
% 4.65/4.83      inference('cnf', [status(esa)], [t74_enumset1])).
% 4.65/4.83  thf('8', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.65/4.83         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 4.65/4.83           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 4.65/4.83              (k1_tarski @ X5)))),
% 4.65/4.83      inference('demod', [status(thm)], ['6', '7'])).
% 4.65/4.83  thf('9', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3)
% 4.65/4.83           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 4.65/4.83      inference('sup+', [status(thm)], ['3', '8'])).
% 4.65/4.83  thf('10', plain,
% 4.65/4.83      (![X83 : $i, X84 : $i, X85 : $i, X86 : $i, X87 : $i]:
% 4.65/4.83         ((k4_enumset1 @ X83 @ X83 @ X84 @ X85 @ X86 @ X87)
% 4.65/4.83           = (k3_enumset1 @ X83 @ X84 @ X85 @ X86 @ X87))),
% 4.65/4.83      inference('cnf', [status(esa)], [t73_enumset1])).
% 4.65/4.83  thf('11', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 4.65/4.83           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 4.65/4.83      inference('demod', [status(thm)], ['9', '10'])).
% 4.65/4.83  thf(t103_enumset1, axiom,
% 4.65/4.83    (![A:$i,B:$i,C:$i,D:$i]:
% 4.65/4.83     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 4.65/4.83  thf('12', plain,
% 4.65/4.83      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X6 @ X7 @ X9 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 4.65/4.83      inference('cnf', [status(esa)], [t103_enumset1])).
% 4.65/4.83  thf('13', plain,
% 4.65/4.83      (![X76 : $i, X77 : $i, X78 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X76 @ X76 @ X77 @ X78)
% 4.65/4.83           = (k1_enumset1 @ X76 @ X77 @ X78))),
% 4.65/4.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.65/4.83  thf('14', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 4.65/4.83      inference('sup+', [status(thm)], ['12', '13'])).
% 4.65/4.83  thf('15', plain,
% 4.65/4.83      (![X76 : $i, X77 : $i, X78 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X76 @ X76 @ X77 @ X78)
% 4.65/4.83           = (k1_enumset1 @ X76 @ X77 @ X78))),
% 4.65/4.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.65/4.83  thf('16', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.65/4.83         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 4.65/4.83      inference('sup+', [status(thm)], ['14', '15'])).
% 4.65/4.83  thf(t69_enumset1, axiom,
% 4.65/4.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.65/4.83  thf('17', plain,
% 4.65/4.83      (![X73 : $i]: ((k2_tarski @ X73 @ X73) = (k1_tarski @ X73))),
% 4.65/4.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.65/4.83  thf(t48_enumset1, axiom,
% 4.65/4.83    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.65/4.83     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 4.65/4.83       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 4.65/4.83  thf('18', plain,
% 4.65/4.83      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 4.65/4.83         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 4.65/4.83           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ 
% 4.65/4.83              (k1_enumset1 @ X16 @ X17 @ X18)))),
% 4.65/4.83      inference('cnf', [status(esa)], [t48_enumset1])).
% 4.65/4.83  thf('19', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 4.65/4.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 4.65/4.83      inference('sup+', [status(thm)], ['17', '18'])).
% 4.65/4.83  thf('20', plain,
% 4.65/4.83      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i]:
% 4.65/4.83         ((k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82)
% 4.65/4.83           = (k2_enumset1 @ X79 @ X80 @ X81 @ X82))),
% 4.65/4.83      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.65/4.83  thf('21', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 4.65/4.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.65/4.83      inference('sup+', [status(thm)], ['19', '20'])).
% 4.65/4.83  thf(commutativity_k2_xboole_0, axiom,
% 4.65/4.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.65/4.83  thf('22', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.65/4.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.65/4.83  thf('23', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 4.65/4.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.65/4.83      inference('sup+', [status(thm)], ['21', '22'])).
% 4.65/4.83  thf('24', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 4.65/4.83           = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 4.65/4.83      inference('sup+', [status(thm)], ['16', '23'])).
% 4.65/4.83  thf('25', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 4.65/4.83           = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 4.65/4.83      inference('demod', [status(thm)], ['11', '24'])).
% 4.65/4.83  thf('26', plain,
% 4.65/4.83      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i]:
% 4.65/4.83         ((k3_enumset1 @ X79 @ X79 @ X80 @ X81 @ X82)
% 4.65/4.83           = (k2_enumset1 @ X79 @ X80 @ X81 @ X82))),
% 4.65/4.83      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.65/4.83  thf('27', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X0 @ X1 @ X3))),
% 4.65/4.83      inference('sup+', [status(thm)], ['25', '26'])).
% 4.65/4.83  thf(t107_enumset1, axiom,
% 4.65/4.83    (![A:$i,B:$i,C:$i,D:$i]:
% 4.65/4.83     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 4.65/4.83  thf('28', plain,
% 4.65/4.83      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 4.65/4.83           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 4.65/4.83      inference('cnf', [status(esa)], [t107_enumset1])).
% 4.65/4.83  thf('29', plain,
% 4.65/4.83      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X6 @ X7 @ X9 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 4.65/4.83      inference('cnf', [status(esa)], [t103_enumset1])).
% 4.65/4.83  thf('30', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.65/4.83      inference('sup+', [status(thm)], ['28', '29'])).
% 4.65/4.83  thf('31', plain,
% 4.65/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.65/4.83      inference('sup+', [status(thm)], ['28', '29'])).
% 4.65/4.83  thf('32', plain,
% 4.65/4.83      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 4.65/4.83         ((k2_enumset1 @ X6 @ X7 @ X9 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 4.65/4.83      inference('cnf', [status(esa)], [t103_enumset1])).
% 4.65/4.83  thf('33', plain,
% 4.65/4.83      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 4.65/4.83         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 4.65/4.83      inference('demod', [status(thm)], ['0', '27', '30', '31', '32'])).
% 4.65/4.83  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 4.65/4.83  
% 4.65/4.83  % SZS output end Refutation
% 4.65/4.83  
% 4.66/4.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
