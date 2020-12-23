%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v6OcMCnFMv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:32 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 133 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  623 (1236 expanded)
%              Number of equality atoms :   62 ( 124 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X14 @ X16 @ X15 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k2_enumset1 @ X60 @ X60 @ X61 @ X62 )
      = ( k1_enumset1 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k1_enumset1 @ sk_A @ sk_C @ sk_B )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X57: $i] :
      ( ( k2_tarski @ X57 @ X57 )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X35 @ X36 @ X37 ) @ ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('13',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k2_enumset1 @ X60 @ X60 @ X61 @ X62 )
      = ( k1_enumset1 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X25 @ X24 @ X23 @ X22 )
      = ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('16',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k2_enumset1 @ X60 @ X60 @ X61 @ X62 )
      = ( k1_enumset1 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('20',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k2_enumset1 @ X60 @ X60 @ X61 @ X62 )
      = ( k1_enumset1 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X57: $i] :
      ( ( k2_tarski @ X57 @ X57 )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X35 @ X36 @ X37 ) @ ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k2_enumset1 @ X60 @ X60 @ X61 @ X62 )
      = ( k1_enumset1 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X57: $i] :
      ( ( k2_tarski @ X57 @ X57 )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X57: $i] :
      ( ( k2_tarski @ X57 @ X57 )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k2_enumset1 @ X60 @ X60 @ X61 @ X62 )
      = ( k1_enumset1 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_enumset1 @ X58 @ X58 @ X59 )
      = ( k2_tarski @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X35 @ X36 @ X37 ) @ ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k2_enumset1 @ X60 @ X60 @ X61 @ X62 )
      = ( k1_enumset1 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('49',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X35 @ X36 @ X37 ) @ ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('50',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( k2_enumset1 @ X60 @ X60 @ X61 @ X62 )
      = ( k1_enumset1 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v6OcMCnFMv
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.56/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.77  % Solved by: fo/fo7.sh
% 0.56/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.77  % done 525 iterations in 0.306s
% 0.56/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.77  % SZS output start Refutation
% 0.56/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.77  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.56/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.77  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.56/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.56/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.77  thf(t137_enumset1, conjecture,
% 0.56/0.77    (![A:$i,B:$i,C:$i]:
% 0.56/0.77     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.56/0.77       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.56/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.77        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.56/0.77          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.56/0.77    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.56/0.77  thf('0', plain,
% 0.56/0.77      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.56/0.77         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(l53_enumset1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.56/0.77       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.56/0.77  thf('1', plain,
% 0.56/0.77      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.56/0.77           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.56/0.77      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.56/0.77  thf('2', plain,
% 0.56/0.77      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.56/0.77         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.56/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.56/0.77  thf(t113_enumset1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 0.56/0.77  thf('3', plain,
% 0.56/0.77      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X17 @ X14 @ X16 @ X15)
% 0.56/0.77           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 0.56/0.77      inference('cnf', [status(esa)], [t113_enumset1])).
% 0.56/0.77  thf(t71_enumset1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i]:
% 0.56/0.77     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.56/0.77  thf('4', plain,
% 0.56/0.77      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X60 @ X60 @ X61 @ X62)
% 0.56/0.77           = (k1_enumset1 @ X60 @ X61 @ X62))),
% 0.56/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.77  thf('5', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.77      inference('sup+', [status(thm)], ['3', '4'])).
% 0.56/0.77  thf('6', plain,
% 0.56/0.77      (((k1_enumset1 @ sk_A @ sk_C @ sk_B)
% 0.56/0.77         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.56/0.77      inference('demod', [status(thm)], ['2', '5'])).
% 0.56/0.77  thf(t69_enumset1, axiom,
% 0.56/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.56/0.77  thf('7', plain, (![X57 : $i]: ((k2_tarski @ X57 @ X57) = (k1_tarski @ X57))),
% 0.56/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.56/0.77  thf(t70_enumset1, axiom,
% 0.56/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.56/0.77  thf('8', plain,
% 0.56/0.77      (![X58 : $i, X59 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.56/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.77  thf('9', plain,
% 0.56/0.77      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.56/0.77           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.56/0.77      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.56/0.77  thf('10', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 0.56/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ 
% 0.56/0.77              (k2_tarski @ X3 @ X2)))),
% 0.56/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.56/0.77  thf('11', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 0.56/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.56/0.77      inference('sup+', [status(thm)], ['7', '10'])).
% 0.56/0.77  thf(t46_enumset1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.56/0.77       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.56/0.77  thf('12', plain,
% 0.56/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 0.56/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X35 @ X36 @ X37) @ (k1_tarski @ X38)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.56/0.77  thf('13', plain,
% 0.56/0.77      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X60 @ X60 @ X61 @ X62)
% 0.56/0.77           = (k1_enumset1 @ X60 @ X61 @ X62))),
% 0.56/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.77  thf('14', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.56/0.77      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.56/0.77  thf(t125_enumset1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.56/0.77  thf('15', plain,
% 0.56/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X25 @ X24 @ X23 @ X22)
% 0.56/0.77           = (k2_enumset1 @ X22 @ X23 @ X24 @ X25))),
% 0.56/0.77      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.56/0.77  thf('16', plain,
% 0.56/0.77      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X60 @ X60 @ X61 @ X62)
% 0.56/0.77           = (k1_enumset1 @ X60 @ X61 @ X62))),
% 0.56/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.77  thf('17', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.77      inference('sup+', [status(thm)], ['15', '16'])).
% 0.56/0.77  thf('18', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.56/0.77  thf('19', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.56/0.77  thf('20', plain,
% 0.56/0.77      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.56/0.77         != (k1_enumset1 @ sk_C @ sk_B @ sk_A))),
% 0.56/0.77      inference('demod', [status(thm)], ['6', '18', '19'])).
% 0.56/0.77  thf('21', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.77      inference('sup+', [status(thm)], ['15', '16'])).
% 0.56/0.77  thf('22', plain,
% 0.56/0.77      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X60 @ X60 @ X61 @ X62)
% 0.56/0.77           = (k1_enumset1 @ X60 @ X61 @ X62))),
% 0.56/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.77  thf('23', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.56/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.56/0.77  thf('24', plain,
% 0.56/0.77      (![X58 : $i, X59 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.56/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.77  thf('25', plain,
% 0.56/0.77      (![X57 : $i]: ((k2_tarski @ X57 @ X57) = (k1_tarski @ X57))),
% 0.56/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.56/0.77  thf('26', plain,
% 0.56/0.77      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.56/0.77      inference('sup+', [status(thm)], ['24', '25'])).
% 0.56/0.77  thf('27', plain,
% 0.56/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 0.56/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X35 @ X36 @ X37) @ (k1_tarski @ X38)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.56/0.77  thf('28', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.56/0.77           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.56/0.77      inference('sup+', [status(thm)], ['26', '27'])).
% 0.56/0.77  thf('29', plain,
% 0.56/0.77      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X60 @ X60 @ X61 @ X62)
% 0.56/0.77           = (k1_enumset1 @ X60 @ X61 @ X62))),
% 0.56/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.77  thf('30', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.56/0.77           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.56/0.77      inference('demod', [status(thm)], ['28', '29'])).
% 0.56/0.77  thf('31', plain,
% 0.56/0.77      (![X57 : $i]: ((k2_tarski @ X57 @ X57) = (k1_tarski @ X57))),
% 0.56/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.56/0.77  thf('32', plain,
% 0.56/0.77      (![X57 : $i]: ((k2_tarski @ X57 @ X57) = (k1_tarski @ X57))),
% 0.56/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.56/0.77  thf('33', plain,
% 0.56/0.77      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.56/0.77           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.56/0.77      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.56/0.77  thf('34', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.56/0.77           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.56/0.77      inference('sup+', [status(thm)], ['32', '33'])).
% 0.56/0.77  thf('35', plain,
% 0.56/0.77      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X60 @ X60 @ X61 @ X62)
% 0.56/0.77           = (k1_enumset1 @ X60 @ X61 @ X62))),
% 0.56/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.77  thf('36', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.56/0.77           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.56/0.77      inference('demod', [status(thm)], ['34', '35'])).
% 0.56/0.77  thf('37', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.56/0.77           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.56/0.77      inference('sup+', [status(thm)], ['31', '36'])).
% 0.56/0.77  thf('38', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.56/0.77      inference('sup+', [status(thm)], ['30', '37'])).
% 0.56/0.77  thf('39', plain,
% 0.56/0.77      (![X58 : $i, X59 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.56/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.77  thf('40', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.56/0.77      inference('sup+', [status(thm)], ['38', '39'])).
% 0.56/0.77  thf('41', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.56/0.77      inference('sup+', [status(thm)], ['23', '40'])).
% 0.56/0.77  thf('42', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.56/0.77      inference('sup+', [status(thm)], ['30', '37'])).
% 0.56/0.77  thf('43', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.56/0.77      inference('sup+', [status(thm)], ['41', '42'])).
% 0.56/0.77  thf('44', plain,
% 0.56/0.77      (![X58 : $i, X59 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X58 @ X58 @ X59) = (k2_tarski @ X58 @ X59))),
% 0.56/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.77  thf('45', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.56/0.77      inference('sup+', [status(thm)], ['43', '44'])).
% 0.56/0.77  thf('46', plain,
% 0.56/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 0.56/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X35 @ X36 @ X37) @ (k1_tarski @ X38)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.56/0.77  thf('47', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2)
% 0.56/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.56/0.77      inference('sup+', [status(thm)], ['45', '46'])).
% 0.56/0.77  thf('48', plain,
% 0.56/0.77      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X60 @ X60 @ X61 @ X62)
% 0.56/0.77           = (k1_enumset1 @ X60 @ X61 @ X62))),
% 0.56/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.77  thf('49', plain,
% 0.56/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 0.56/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X35 @ X36 @ X37) @ (k1_tarski @ X38)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.56/0.77  thf('50', plain,
% 0.56/0.77      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.56/0.77         ((k2_enumset1 @ X60 @ X60 @ X61 @ X62)
% 0.56/0.77           = (k1_enumset1 @ X60 @ X61 @ X62))),
% 0.56/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.77  thf('51', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.77         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.56/0.77      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.56/0.77  thf('52', plain,
% 0.56/0.77      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.56/0.77         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.56/0.77      inference('demod', [status(thm)], ['20', '51'])).
% 0.56/0.77  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.56/0.77  
% 0.56/0.77  % SZS output end Refutation
% 0.56/0.77  
% 0.56/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
