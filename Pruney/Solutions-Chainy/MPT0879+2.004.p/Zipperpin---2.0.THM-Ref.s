%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MaxTUezVlM

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 150 expanded)
%              Number of leaves         :   31 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  583 (1603 expanded)
%              Number of equality atoms :   50 ( 135 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('0',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k4_mcart_1 @ X42 @ X43 @ X44 @ X45 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X42 @ X43 ) @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X46 @ X47 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t39_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
      = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
        = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_mcart_1])).

thf('3',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X29 ) @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_tarski @ ( k4_tarski @ X29 @ X30 ) @ ( k4_tarski @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(t86_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X24 @ X24 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t86_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k6_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k5_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X24 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X21: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X21: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf(t78_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X18 @ X18 @ X18 @ X19 @ X20 )
      = ( k1_enumset1 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t83_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X22 @ X22 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X18 @ X18 @ X18 @ X19 @ X20 )
      = ( k1_enumset1 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k3_zfmisc_1 @ X35 @ X36 @ X37 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) )
      = ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) )
     != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','29'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('31',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k4_mcart_1 @ X38 @ X39 @ X40 @ X41 )
      = ( k4_tarski @ ( k3_mcart_1 @ X38 @ X39 @ X40 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('32',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X46 @ X47 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['30','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MaxTUezVlM
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 202 iterations in 0.085s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.53                                           $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.53  thf(t31_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.53       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.53         ((k4_mcart_1 @ X42 @ X43 @ X44 @ X45)
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X42 @ X43) @ X44) @ X45))),
% 0.20/0.53      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.20/0.53  thf(t7_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X46 : $i, X47 : $i]: ((k1_mcart_1 @ (k4_tarski @ X46 @ X47)) = (X46))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(t39_mcart_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_zfmisc_1 @
% 0.20/0.53         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.53       ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( k3_zfmisc_1 @
% 0.20/0.53            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.53          ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t39_mcart_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.20/0.53         (k1_tarski @ sk_C)) != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t36_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.53         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.20/0.53       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.20/0.53         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         ((k2_zfmisc_1 @ (k1_tarski @ X29) @ (k2_tarski @ X30 @ X31))
% 0.20/0.53           = (k2_tarski @ (k4_tarski @ X29 @ X30) @ (k4_tarski @ X29 @ X31)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.20/0.53  thf(t86_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.53     ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.53       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         ((k6_enumset1 @ X24 @ X24 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.20/0.53           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [t86_enumset1])).
% 0.20/0.53  thf(t75_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.53     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.53       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         ((k6_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.53           = (k5_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X24 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.20/0.53           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.20/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(t82_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X21 : $i]: ((k2_enumset1 @ X21 @ X21 @ X21 @ X21) = (k1_tarski @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.20/0.53  thf(l68_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.53     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.53       ( k2_xboole_0 @
% 0.20/0.53         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.20/0.53              (k1_enumset1 @ X4 @ X5 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf(t44_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k1_enumset1 @ X8 @ X9 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.20/0.53           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X21 : $i]: ((k2_enumset1 @ X21 @ X21 @ X21 @ X21) = (k1_tarski @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['7', '14'])).
% 0.20/0.53  thf(t78_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_enumset1 @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((k3_enumset1 @ X18 @ X18 @ X18 @ X19 @ X20)
% 0.20/0.53           = (k1_enumset1 @ X18 @ X19 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t78_enumset1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t83_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k3_enumset1 @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         ((k3_enumset1 @ X22 @ X22 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t83_enumset1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((k3_enumset1 @ X18 @ X18 @ X18 @ X19 @ X20)
% 0.20/0.53           = (k1_enumset1 @ X18 @ X19 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t78_enumset1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.20/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_tarski @ (k4_tarski @ X1 @ X0))
% 0.20/0.53           = (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '21'])).
% 0.20/0.53  thf('23', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_tarski @ (k4_tarski @ X1 @ X0))
% 0.20/0.53           = (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf(d3_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.53       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X35 @ X36 @ X37)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36) @ X37))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.20/0.53           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.20/0.53      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k1_tarski @ (k4_tarski @ X1 @ X0))
% 0.20/0.53           = (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k1_tarski @ (k4_tarski @ (k4_tarski @ X2 @ X1) @ X0))
% 0.20/0.53           = (k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ 
% 0.20/0.53              (k1_tarski @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((k1_tarski @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.53         != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k1_tarski @ (k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ X0)))
% 0.20/0.53           != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '29'])).
% 0.20/0.53  thf(d4_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.53       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.53         ((k4_mcart_1 @ X38 @ X39 @ X40 @ X41)
% 0.20/0.53           = (k4_tarski @ (k3_mcart_1 @ X38 @ X39 @ X40) @ X41))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X46 : $i, X47 : $i]: ((k1_mcart_1 @ (k4_tarski @ X46 @ X47)) = (X46))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.53           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain, ($false),
% 0.20/0.53      inference('simplify_reflect+', [status(thm)], ['30', '33'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
