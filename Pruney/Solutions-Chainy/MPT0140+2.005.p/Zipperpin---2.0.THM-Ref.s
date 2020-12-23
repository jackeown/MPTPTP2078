%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7aKAPEh6ji

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  76 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  686 ( 881 expanded)
%              Number of equality atoms :   43 (  60 expanded)
%              Maximal formula depth    :   17 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t56_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
        = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k5_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7aKAPEh6ji
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 59 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(t56_enumset1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.53     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.53       ( k2_xboole_0 @
% 0.21/0.53         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.53        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.53          ( k2_xboole_0 @
% 0.21/0.53            ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t56_enumset1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.53         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.53             (k4_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t51_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.53     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.53         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.21/0.53              (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.21/0.53  thf(t41_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k2_tarski @ A @ B ) =
% 0.21/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         ((k2_tarski @ X12 @ X13)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.53  thf(t4_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.53       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.53              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.21/0.53           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.21/0.53              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.53         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.21/0.53             (k3_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.53  thf(t54_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.53     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.53       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         ((k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.21/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X28 @ X29 @ X30 @ X31) @ 
% 0.21/0.53              (k2_tarski @ X32 @ X33)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.21/0.53  thf(t47_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.53     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 0.21/0.53              (k2_enumset1 @ X18 @ X19 @ X20 @ X21)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.21/0.53              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X5)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.53           (k2_tarski @ X1 @ X0))
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.21/0.53              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         ((k2_tarski @ X12 @ X13)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.53  thf(t55_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.53     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.53       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.53         ((k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.21/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38) @ 
% 0.21/0.53              (k1_tarski @ X39)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 0.21/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.21/0.53              (k2_xboole_0 @ (k1_tarski @ X0) @ X6)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.21/0.53           (k1_tarski @ X0))
% 0.21/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.53              (k2_tarski @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['12', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         ((k2_tarski @ X12 @ X13)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.53              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf(t42_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.53           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         ((k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.21/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X28 @ X29 @ X30 @ X31) @ 
% 0.21/0.53              (k2_tarski @ X32 @ X33)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 0.21/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.53              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X6)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.21/0.53           (k1_tarski @ X0))
% 0.21/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 0.21/0.53              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['21', '24'])).
% 0.21/0.53  thf(l68_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.53     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.53       ( k2_xboole_0 @
% 0.21/0.53         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         ((k5_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X6 @ X7 @ X8) @ 
% 0.21/0.53              (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.21/0.53           (k1_tarski @ X0)) = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.53           (k2_tarski @ X1 @ X0))
% 0.21/0.53           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['16', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.21/0.53              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.21/0.53           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.21/0.53              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.21/0.53           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.53           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.53         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '31'])).
% 0.21/0.53  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
