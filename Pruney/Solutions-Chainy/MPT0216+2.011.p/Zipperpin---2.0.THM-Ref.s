%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GPCogegUEJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:59 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  487 ( 886 expanded)
%              Number of equality atoms :   47 ( 120 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t9_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( B = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( B = C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_zfmisc_1])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( A = B ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X29 = X28 )
      | ( ( k1_tarski @ X29 )
       != ( k2_tarski @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A = sk_B ),
    inference(eq_res,[status(thm)],['10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ sk_B @ sk_C )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ sk_B @ sk_C )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) )
      = ( k1_enumset1 @ X0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) ) @ ( k1_enumset1 @ X0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_B ) ) @ ( k2_tarski @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_B ) ) @ ( k2_xboole_0 @ X0 @ ( k2_tarski @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_B ) ) @ ( k2_enumset1 @ X1 @ X0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_B ) ) @ ( k1_enumset1 @ X0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_B ) ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['2','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('29',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('31',plain,(
    r1_tarski @ ( k1_tarski @ sk_C ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_C @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_C @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_C @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('39',plain,
    ( ( k2_enumset1 @ sk_B @ sk_C @ sk_B @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['31','36','39'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('42',plain,(
    sk_C = sk_B ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GPCogegUEJ
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 380 iterations in 0.143s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(t100_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.39/0.59      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.39/0.59  thf(t70_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.39/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf(t71_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.39/0.59           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.39/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.59  thf(l53_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.39/0.59       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.59           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.39/0.59      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf(t69_enumset1, axiom,
% 0.39/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.59  thf('6', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.59  thf(t9_zfmisc_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.59        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t9_zfmisc_1])).
% 0.39/0.59  thf('7', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('8', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t8_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ))).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.59         (((X29) = (X28)) | ((k1_tarski @ X29) != (k2_tarski @ X28 @ X30)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t8_zfmisc_1])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X0 : $i]: (((k1_tarski @ X0) != (k1_tarski @ sk_A)) | ((X0) = (sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.59  thf('11', plain, (((sk_A) = (sk_B))),
% 0.39/0.59      inference('eq_res', [status(thm)], ['10'])).
% 0.39/0.59  thf('12', plain, (((k1_tarski @ sk_B) = (k2_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.59           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.39/0.59      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X1 @ X0 @ sk_B @ sk_C)
% 0.39/0.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ sk_B)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X0 @ X0 @ sk_B @ sk_C)
% 0.39/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_B)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['6', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.39/0.59           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.39/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_B))
% 0.39/0.59           = (k1_enumset1 @ X0 @ sk_B @ sk_C))),
% 0.39/0.59      inference('sup+', [status(thm)], ['15', '16'])).
% 0.39/0.59  thf(t40_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X8 : $i, X9 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.39/0.59           = (k4_xboole_0 @ X8 @ X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.59  thf(t36_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.39/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_B)) @ 
% 0.39/0.59          (k1_enumset1 @ X0 @ sk_B @ sk_C))),
% 0.39/0.59      inference('sup+', [status(thm)], ['17', '20'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_B)) @ 
% 0.39/0.59        (k2_tarski @ sk_C @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['5', '21'])).
% 0.39/0.59  thf(t10_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X1 @ X2) | (r1_tarski @ X1 @ (k2_xboole_0 @ X3 @ X2)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (r1_tarski @ 
% 0.39/0.59          (k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_B)) @ 
% 0.39/0.59          (k2_xboole_0 @ X0 @ (k2_tarski @ sk_C @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (r1_tarski @ 
% 0.39/0.59          (k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_B)) @ 
% 0.39/0.59          (k2_enumset1 @ X1 @ X0 @ sk_C @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['4', '24'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (r1_tarski @ 
% 0.39/0.59          (k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_B)) @ 
% 0.39/0.59          (k1_enumset1 @ X0 @ sk_C @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['3', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_B)) @ 
% 0.39/0.59        (k2_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('sup+', [status(thm)], ['2', '26'])).
% 0.39/0.59  thf('28', plain, (((k1_tarski @ sk_B) = (k2_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '11'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_B)) @ 
% 0.39/0.59        (k1_tarski @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.59  thf(t44_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.39/0.59       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.59         ((r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.39/0.59          | ~ (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      ((r1_tarski @ (k1_tarski @ sk_C) @ 
% 0.39/0.59        (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.59  thf('33', plain, (((k1_tarski @ sk_B) = (k2_tarski @ sk_B @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '11'])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.59           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.39/0.59      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k2_enumset1 @ sk_B @ sk_C @ X1 @ X0)
% 0.39/0.59           = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ X1 @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k2_enumset1 @ sk_B @ sk_C @ X0 @ X0)
% 0.39/0.59           = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['32', '35'])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k2_enumset1 @ sk_B @ sk_C @ X0 @ X0)
% 0.39/0.59           = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['32', '35'])).
% 0.39/0.59  thf(idempotence_k2_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.59  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (((k2_enumset1 @ sk_B @ sk_C @ sk_B @ sk_B) = (k1_tarski @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['37', '38'])).
% 0.39/0.59  thf('40', plain, ((r1_tarski @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.39/0.59  thf(t6_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.39/0.59       ( ( A ) = ( B ) ) ))).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (![X26 : $i, X27 : $i]:
% 0.39/0.59         (((X27) = (X26))
% 0.39/0.59          | ~ (r1_tarski @ (k1_tarski @ X27) @ (k1_tarski @ X26)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.39/0.59  thf('42', plain, (((sk_C) = (sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.59  thf('43', plain, (((sk_B) != (sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('44', plain, ($false),
% 0.39/0.59      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
