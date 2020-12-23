%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mwyJibLllZ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:32 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 107 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  614 (1204 expanded)
%              Number of equality atoms :   48 (  95 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t72_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_enumset1 @ A @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t72_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_enumset1 @ X61 @ X61 @ X62 )
      = ( k2_tarski @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X60: $i] :
      ( ( k2_tarski @ X60 @ X60 )
      = ( k1_tarski @ X60 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X1 @ X0 @ X3 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mwyJibLllZ
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:06:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 549 iterations in 0.324s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.79  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.59/0.79  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.79  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(t72_enumset1, conjecture,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79        ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t72_enumset1])).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (((k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.59/0.79         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t71_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 0.59/0.79           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.79  thf(t70_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X61 : $i, X62 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X61 @ X61 @ X62) = (k2_tarski @ X61 @ X62))),
% 0.59/0.79      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.79  thf(t44_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['2', '3'])).
% 0.59/0.79  thf(t69_enumset1, axiom,
% 0.59/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.79  thf('5', plain, (![X60 : $i]: ((k2_tarski @ X60 @ X60) = (k1_tarski @ X60))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf(l53_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.59/0.79           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.59/0.79      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 0.59/0.79           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['7', '8'])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '9'])).
% 0.59/0.79  thf(t47_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.79     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X20) @ 
% 0.59/0.79              (k2_enumset1 @ X21 @ X22 @ X23 @ X24)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['10', '11'])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.59/0.79           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf(t55_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.79     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.59/0.79           = (k2_xboole_0 @ (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35) @ 
% 0.59/0.79              (k1_tarski @ X36)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 @ X4)
% 0.59/0.79           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.59/0.79              (k1_tarski @ X4)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X2 @ X2 @ X1 @ X1 @ X0 @ X3)
% 0.59/0.79           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['1', '16'])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 0.59/0.79           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X20) @ 
% 0.59/0.79              (k2_enumset1 @ X21 @ X22 @ X23 @ X24)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['18', '19'])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf(t51_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.79     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X25) @ 
% 0.59/0.79              (k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.59/0.79              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['22', '23'])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X20) @ 
% 0.59/0.79              (k2_enumset1 @ X21 @ X22 @ X23 @ X24)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['24', '25'])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.59/0.79           = (k2_xboole_0 @ (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35) @ 
% 0.59/0.79              (k1_tarski @ X36)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 @ X4)
% 0.59/0.79           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.59/0.79              (k1_tarski @ X4)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X2 @ X1) @ 
% 0.59/0.79              (k1_tarski @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['26', '29'])).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '9'])).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.59/0.79  thf('34', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X2 @ X2 @ X1 @ X1 @ X0 @ X3)
% 0.59/0.79           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 0.59/0.79      inference('demod', [status(thm)], ['17', '33'])).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.79         ((k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['24', '25'])).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['34', '35'])).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.59/0.79         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['0', '36'])).
% 0.59/0.79  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
