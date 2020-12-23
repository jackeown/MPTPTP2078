%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YqheAmKxtQ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:29 EST 2020

% Result     : Timeout 58.03s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   67 (  85 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  708 ( 874 expanded)
%              Number of equality atoms :   53 (  71 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t45_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','19'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k3_mcart_1 @ X35 @ X36 @ X37 )
      = ( k4_tarski @ ( k4_tarski @ X35 @ X36 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('22',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k3_mcart_1 @ X35 @ X36 @ X37 )
      = ( k4_tarski @ ( k4_tarski @ X35 @ X36 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X27 @ X30 ) @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X27 @ X28 ) @ ( k4_tarski @ X27 @ X29 ) @ ( k4_tarski @ X30 @ X28 ) @ ( k4_tarski @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k3_mcart_1 @ X35 @ X36 @ X37 )
      = ( k4_tarski @ ( k4_tarski @ X35 @ X36 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k3_mcart_1 @ X35 @ X36 @ X37 )
      = ( k4_tarski @ ( k4_tarski @ X35 @ X36 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('33',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X2 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X2 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('36',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k3_zfmisc_1 @ X38 @ X39 @ X40 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('37',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['20','29','34','35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YqheAmKxtQ
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 58.03/58.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 58.03/58.35  % Solved by: fo/fo7.sh
% 58.03/58.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 58.03/58.35  % done 17947 iterations in 57.897s
% 58.03/58.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 58.03/58.35  % SZS output start Refutation
% 58.03/58.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 58.03/58.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 58.03/58.35  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 58.03/58.35  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 58.03/58.35  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 58.03/58.35  thf(sk_B_type, type, sk_B: $i).
% 58.03/58.35  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 58.03/58.35  thf(sk_D_type, type, sk_D: $i).
% 58.03/58.35  thf(sk_C_type, type, sk_C: $i).
% 58.03/58.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 58.03/58.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 58.03/58.35  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 58.03/58.35  thf(sk_A_type, type, sk_A: $i).
% 58.03/58.35  thf(sk_E_type, type, sk_E: $i).
% 58.03/58.35  thf(t45_mcart_1, conjecture,
% 58.03/58.35    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 58.03/58.35     ( ( k3_zfmisc_1 @
% 58.03/58.35         ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 58.03/58.35       ( k2_enumset1 @
% 58.03/58.35         ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 58.03/58.35         ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ))).
% 58.03/58.35  thf(zf_stmt_0, negated_conjecture,
% 58.03/58.35    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 58.03/58.35        ( ( k3_zfmisc_1 @
% 58.03/58.35            ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 58.03/58.35          ( k2_enumset1 @
% 58.03/58.35            ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 58.03/58.35            ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )),
% 58.03/58.35    inference('cnf.neg', [status(esa)], [t45_mcart_1])).
% 58.03/58.35  thf('0', plain,
% 58.03/58.35      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 58.03/58.35         (k2_tarski @ sk_D @ sk_E))
% 58.03/58.35         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 58.03/58.35             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 58.03/58.35             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 58.03/58.35             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 58.03/58.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.03/58.35  thf(t70_enumset1, axiom,
% 58.03/58.35    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 58.03/58.35  thf('1', plain,
% 58.03/58.35      (![X20 : $i, X21 : $i]:
% 58.03/58.35         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 58.03/58.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 58.03/58.35  thf(t69_enumset1, axiom,
% 58.03/58.35    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 58.03/58.35  thf('2', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 58.03/58.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 58.03/58.35  thf('3', plain,
% 58.03/58.35      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 58.03/58.35      inference('sup+', [status(thm)], ['1', '2'])).
% 58.03/58.35  thf(t41_enumset1, axiom,
% 58.03/58.35    (![A:$i,B:$i]:
% 58.03/58.35     ( ( k2_tarski @ A @ B ) =
% 58.03/58.35       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 58.03/58.35  thf('4', plain,
% 58.03/58.35      (![X6 : $i, X7 : $i]:
% 58.03/58.35         ((k2_tarski @ X6 @ X7)
% 58.03/58.35           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X7)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t41_enumset1])).
% 58.03/58.35  thf(commutativity_k2_xboole_0, axiom,
% 58.03/58.35    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 58.03/58.35  thf('5', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 58.03/58.35      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 58.03/58.35  thf('6', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i]:
% 58.03/58.35         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 58.03/58.35           = (k2_tarski @ X1 @ X0))),
% 58.03/58.35      inference('sup+', [status(thm)], ['4', '5'])).
% 58.03/58.35  thf('7', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i]:
% 58.03/58.35         ((k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k1_tarski @ X1))
% 58.03/58.35           = (k2_tarski @ X1 @ X0))),
% 58.03/58.35      inference('sup+', [status(thm)], ['3', '6'])).
% 58.03/58.35  thf(t46_enumset1, axiom,
% 58.03/58.35    (![A:$i,B:$i,C:$i,D:$i]:
% 58.03/58.35     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 58.03/58.35       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 58.03/58.35  thf('8', plain,
% 58.03/58.35      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 58.03/58.35           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t46_enumset1])).
% 58.03/58.35  thf(t71_enumset1, axiom,
% 58.03/58.35    (![A:$i,B:$i,C:$i]:
% 58.03/58.35     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 58.03/58.35  thf('9', plain,
% 58.03/58.35      (![X22 : $i, X23 : $i, X24 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 58.03/58.35           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 58.03/58.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 58.03/58.35  thf('10', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i]:
% 58.03/58.35         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 58.03/58.35      inference('demod', [status(thm)], ['7', '8', '9'])).
% 58.03/58.35  thf('11', plain,
% 58.03/58.35      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 58.03/58.35           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t46_enumset1])).
% 58.03/58.35  thf('12', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2)
% 58.03/58.35           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 58.03/58.35      inference('sup+', [status(thm)], ['10', '11'])).
% 58.03/58.35  thf('13', plain,
% 58.03/58.35      (![X22 : $i, X23 : $i, X24 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 58.03/58.35           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 58.03/58.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 58.03/58.35  thf(t43_enumset1, axiom,
% 58.03/58.35    (![A:$i,B:$i,C:$i]:
% 58.03/58.35     ( ( k1_enumset1 @ A @ B @ C ) =
% 58.03/58.35       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 58.03/58.35  thf('14', plain,
% 58.03/58.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 58.03/58.35         ((k1_enumset1 @ X8 @ X9 @ X10)
% 58.03/58.35           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X10)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t43_enumset1])).
% 58.03/58.35  thf('15', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.03/58.35         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 58.03/58.35      inference('demod', [status(thm)], ['12', '13', '14'])).
% 58.03/58.35  thf(t44_enumset1, axiom,
% 58.03/58.35    (![A:$i,B:$i,C:$i,D:$i]:
% 58.03/58.35     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 58.03/58.35       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 58.03/58.35  thf('16', plain,
% 58.03/58.35      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 58.03/58.35           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t44_enumset1])).
% 58.03/58.35  thf('17', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0)
% 58.03/58.35           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 58.03/58.35      inference('sup+', [status(thm)], ['15', '16'])).
% 58.03/58.35  thf('18', plain,
% 58.03/58.35      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 58.03/58.35           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t44_enumset1])).
% 58.03/58.35  thf('19', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 58.03/58.35         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 58.03/58.35      inference('sup+', [status(thm)], ['17', '18'])).
% 58.03/58.35  thf('20', plain,
% 58.03/58.35      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 58.03/58.35         (k2_tarski @ sk_D @ sk_E))
% 58.03/58.35         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 58.03/58.35             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 58.03/58.35             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 58.03/58.35             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 58.03/58.35      inference('demod', [status(thm)], ['0', '19'])).
% 58.03/58.35  thf(d3_mcart_1, axiom,
% 58.03/58.35    (![A:$i,B:$i,C:$i]:
% 58.03/58.35     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 58.03/58.35  thf('21', plain,
% 58.03/58.35      (![X35 : $i, X36 : $i, X37 : $i]:
% 58.03/58.35         ((k3_mcart_1 @ X35 @ X36 @ X37)
% 58.03/58.35           = (k4_tarski @ (k4_tarski @ X35 @ X36) @ X37))),
% 58.03/58.35      inference('cnf', [status(esa)], [d3_mcart_1])).
% 58.03/58.35  thf('22', plain,
% 58.03/58.35      (![X35 : $i, X36 : $i, X37 : $i]:
% 58.03/58.35         ((k3_mcart_1 @ X35 @ X36 @ X37)
% 58.03/58.35           = (k4_tarski @ (k4_tarski @ X35 @ X36) @ X37))),
% 58.03/58.35      inference('cnf', [status(esa)], [d3_mcart_1])).
% 58.03/58.35  thf(t146_zfmisc_1, axiom,
% 58.03/58.35    (![A:$i,B:$i,C:$i,D:$i]:
% 58.03/58.35     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 58.03/58.35       ( k2_enumset1 @
% 58.03/58.35         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 58.03/58.35         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 58.03/58.35  thf('23', plain,
% 58.03/58.35      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 58.03/58.35         ((k2_zfmisc_1 @ (k2_tarski @ X27 @ X30) @ (k2_tarski @ X28 @ X29))
% 58.03/58.35           = (k2_enumset1 @ (k4_tarski @ X27 @ X28) @ 
% 58.03/58.35              (k4_tarski @ X27 @ X29) @ (k4_tarski @ X30 @ X28) @ 
% 58.03/58.35              (k4_tarski @ X30 @ X29)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 58.03/58.35  thf('24', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 58.03/58.35         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 58.03/58.35           (k2_tarski @ X0 @ X3))
% 58.03/58.35           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 58.03/58.35              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 58.03/58.35              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 58.03/58.35      inference('sup+', [status(thm)], ['22', '23'])).
% 58.03/58.35  thf('25', plain,
% 58.03/58.35      (![X35 : $i, X36 : $i, X37 : $i]:
% 58.03/58.35         ((k3_mcart_1 @ X35 @ X36 @ X37)
% 58.03/58.35           = (k4_tarski @ (k4_tarski @ X35 @ X36) @ X37))),
% 58.03/58.35      inference('cnf', [status(esa)], [d3_mcart_1])).
% 58.03/58.35  thf('26', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 58.03/58.35         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 58.03/58.35           (k2_tarski @ X0 @ X3))
% 58.03/58.35           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 58.03/58.35              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 58.03/58.35              (k4_tarski @ X4 @ X3)))),
% 58.03/58.35      inference('demod', [status(thm)], ['24', '25'])).
% 58.03/58.35  thf('27', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 58.03/58.35         ((k2_zfmisc_1 @ 
% 58.03/58.35           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 58.03/58.35           (k2_tarski @ X0 @ X3))
% 58.03/58.35           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 58.03/58.35              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 58.03/58.35              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 58.03/58.35      inference('sup+', [status(thm)], ['21', '26'])).
% 58.03/58.35  thf('28', plain,
% 58.03/58.35      (![X35 : $i, X36 : $i, X37 : $i]:
% 58.03/58.35         ((k3_mcart_1 @ X35 @ X36 @ X37)
% 58.03/58.35           = (k4_tarski @ (k4_tarski @ X35 @ X36) @ X37))),
% 58.03/58.35      inference('cnf', [status(esa)], [d3_mcart_1])).
% 58.03/58.35  thf('29', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 58.03/58.35         ((k2_zfmisc_1 @ 
% 58.03/58.35           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 58.03/58.35           (k2_tarski @ X0 @ X3))
% 58.03/58.35           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 58.03/58.35              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 58.03/58.35              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 58.03/58.35      inference('demod', [status(thm)], ['27', '28'])).
% 58.03/58.35  thf('30', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i]:
% 58.03/58.35         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 58.03/58.35           = (k2_tarski @ X1 @ X0))),
% 58.03/58.35      inference('sup+', [status(thm)], ['4', '5'])).
% 58.03/58.35  thf('31', plain,
% 58.03/58.35      (![X6 : $i, X7 : $i]:
% 58.03/58.35         ((k2_tarski @ X6 @ X7)
% 58.03/58.35           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X7)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t41_enumset1])).
% 58.03/58.35  thf('32', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 58.03/58.35      inference('sup+', [status(thm)], ['30', '31'])).
% 58.03/58.35  thf(t36_zfmisc_1, axiom,
% 58.03/58.35    (![A:$i,B:$i,C:$i]:
% 58.03/58.35     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 58.03/58.35         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 58.03/58.35       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 58.03/58.35         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 58.03/58.35  thf('33', plain,
% 58.03/58.35      (![X31 : $i, X32 : $i, X33 : $i]:
% 58.03/58.35         ((k2_zfmisc_1 @ (k1_tarski @ X31) @ (k2_tarski @ X32 @ X33))
% 58.03/58.35           = (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X31 @ X33)))),
% 58.03/58.35      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 58.03/58.35  thf('34', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.03/58.35         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X2))
% 58.03/58.35           = (k2_tarski @ (k4_tarski @ X1 @ X2) @ (k4_tarski @ X1 @ X0)))),
% 58.03/58.35      inference('sup+', [status(thm)], ['32', '33'])).
% 58.03/58.35  thf('35', plain,
% 58.03/58.35      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 58.03/58.35      inference('sup+', [status(thm)], ['30', '31'])).
% 58.03/58.35  thf(d3_zfmisc_1, axiom,
% 58.03/58.35    (![A:$i,B:$i,C:$i]:
% 58.03/58.35     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 58.03/58.35       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 58.03/58.35  thf('36', plain,
% 58.03/58.35      (![X38 : $i, X39 : $i, X40 : $i]:
% 58.03/58.35         ((k3_zfmisc_1 @ X38 @ X39 @ X40)
% 58.03/58.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39) @ X40))),
% 58.03/58.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 58.03/58.35  thf('37', plain,
% 58.03/58.35      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 58.03/58.35         (k2_tarski @ sk_D @ sk_E))
% 58.03/58.35         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 58.03/58.35             (k2_tarski @ sk_D @ sk_E)))),
% 58.03/58.35      inference('demod', [status(thm)], ['20', '29', '34', '35', '36'])).
% 58.03/58.35  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 58.03/58.35  
% 58.03/58.35  % SZS output end Refutation
% 58.03/58.35  
% 58.03/58.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
