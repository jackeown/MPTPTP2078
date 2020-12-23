%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DSzAOpBv4J

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:56 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   63 (  70 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  573 ( 657 expanded)
%              Number of equality atoms :   51 (  60 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('0',plain,(
    ! [X45: $i,X47: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X45 ) @ X47 )
        = ( k1_tarski @ X45 ) )
      | ( r2_hidden @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t29_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k2_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_zfmisc_1])).

thf('3',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','27','28'])).

thf('30',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('32',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DSzAOpBv4J
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 323 iterations in 0.187s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.45/0.63                                           $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(l33_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.63       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (![X45 : $i, X47 : $i]:
% 0.45/0.63         (((k4_xboole_0 @ (k1_tarski @ X45) @ X47) = (k1_tarski @ X45))
% 0.45/0.63          | (r2_hidden @ X45 @ X47))),
% 0.45/0.63      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.45/0.63  thf(t98_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ X2 @ X3)
% 0.45/0.63           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.45/0.63            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.45/0.63          | (r2_hidden @ X0 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['0', '1'])).
% 0.48/0.63  thf(t29_zfmisc_1, conjecture,
% 0.48/0.63    (![A:$i,B:$i]:
% 0.48/0.63     ( ( ( A ) != ( B ) ) =>
% 0.48/0.63       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.48/0.63         ( k2_tarski @ A @ B ) ) ))).
% 0.48/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.63    (~( ![A:$i,B:$i]:
% 0.48/0.63        ( ( ( A ) != ( B ) ) =>
% 0.48/0.63          ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.48/0.63            ( k2_tarski @ A @ B ) ) ) )),
% 0.48/0.63    inference('cnf.neg', [status(esa)], [t29_zfmisc_1])).
% 0.48/0.63  thf('3', plain,
% 0.48/0.63      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.48/0.63         != (k2_tarski @ sk_A @ sk_B))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('4', plain,
% 0.48/0.63      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.48/0.63          != (k2_tarski @ sk_A @ sk_B))
% 0.48/0.63        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.63  thf(t70_enumset1, axiom,
% 0.48/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.48/0.63  thf('5', plain,
% 0.48/0.63      (![X18 : $i, X19 : $i]:
% 0.48/0.63         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.48/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.63  thf(t69_enumset1, axiom,
% 0.48/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.63  thf('6', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.48/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.63  thf('7', plain,
% 0.48/0.63      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.48/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.48/0.63  thf(t71_enumset1, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i]:
% 0.48/0.63     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.48/0.63  thf('8', plain,
% 0.48/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.48/0.63         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.48/0.63           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.48/0.63      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.48/0.63  thf(t72_enumset1, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.63     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.48/0.63  thf('9', plain,
% 0.48/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.63         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.48/0.63           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.48/0.63      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.63  thf(t74_enumset1, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.48/0.63     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.48/0.63       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.48/0.63  thf('10', plain,
% 0.48/0.63      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.48/0.63         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.48/0.63           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.48/0.63      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.48/0.63  thf(t68_enumset1, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.48/0.63     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.48/0.63       ( k2_xboole_0 @
% 0.48/0.63         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.48/0.63  thf('11', plain,
% 0.48/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 0.48/0.63         X16 : $i]:
% 0.48/0.63         ((k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.48/0.63           = (k2_xboole_0 @ 
% 0.48/0.63              (k5_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 0.48/0.63              (k1_tarski @ X16)))),
% 0.48/0.63      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.48/0.63  thf('12', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.48/0.63         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.48/0.63           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.48/0.63              (k1_tarski @ X6)))),
% 0.48/0.63      inference('sup+', [status(thm)], ['10', '11'])).
% 0.48/0.63  thf(t75_enumset1, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.48/0.63     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.48/0.63       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.48/0.63  thf('13', plain,
% 0.48/0.63      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.63         ((k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.48/0.63           = (k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 0.48/0.63      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.48/0.63  thf('14', plain,
% 0.48/0.63      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.48/0.63         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.48/0.63           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.48/0.63      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.48/0.63  thf('15', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.63         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.63           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.48/0.63      inference('sup+', [status(thm)], ['13', '14'])).
% 0.48/0.63  thf('16', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.63         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.48/0.63           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.48/0.63      inference('sup+', [status(thm)], ['12', '15'])).
% 0.48/0.63  thf(t73_enumset1, axiom,
% 0.48/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.48/0.63     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.48/0.63       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.48/0.63  thf('17', plain,
% 0.48/0.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.48/0.63         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.48/0.63           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.48/0.63      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.63  thf('18', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.63         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.48/0.63           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.48/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.48/0.63  thf('19', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.63         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 0.48/0.63           = (k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 0.48/0.63      inference('sup+', [status(thm)], ['9', '18'])).
% 0.48/0.63  thf('20', plain,
% 0.48/0.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.48/0.63         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.48/0.63           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.48/0.63      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.63  thf('21', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.63         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 0.48/0.63           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 0.48/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.48/0.63  thf('22', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.48/0.63           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 0.48/0.63      inference('sup+', [status(thm)], ['8', '21'])).
% 0.48/0.63  thf('23', plain,
% 0.48/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.63         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.48/0.63           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.48/0.63      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.63  thf('24', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.48/0.63           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 0.48/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.63  thf('25', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.48/0.63           = (k2_enumset1 @ X0 @ X0 @ X0 @ X1))),
% 0.48/0.63      inference('sup+', [status(thm)], ['7', '24'])).
% 0.48/0.63  thf('26', plain,
% 0.48/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.48/0.63         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.48/0.63           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.48/0.63      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.48/0.63  thf('27', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.48/0.63           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.48/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.48/0.63  thf('28', plain,
% 0.48/0.63      (![X18 : $i, X19 : $i]:
% 0.48/0.63         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.48/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.63  thf('29', plain,
% 0.48/0.63      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.48/0.63        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.63      inference('demod', [status(thm)], ['4', '27', '28'])).
% 0.48/0.63  thf('30', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.48/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.48/0.63  thf(d1_tarski, axiom,
% 0.48/0.63    (![A:$i,B:$i]:
% 0.48/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.48/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.48/0.63  thf('31', plain,
% 0.48/0.63      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.48/0.63         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.48/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.63  thf('32', plain,
% 0.48/0.63      (![X4 : $i, X7 : $i]:
% 0.48/0.63         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.48/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.48/0.63  thf('33', plain, (((sk_B) = (sk_A))),
% 0.48/0.63      inference('sup-', [status(thm)], ['30', '32'])).
% 0.48/0.63  thf('34', plain, (((sk_A) != (sk_B))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('35', plain, ($false),
% 0.48/0.63      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.48/0.63  
% 0.48/0.63  % SZS output end Refutation
% 0.48/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
