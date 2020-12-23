%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Uhba3XbBe

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 253 expanded)
%              Number of leaves         :   17 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  503 (2625 expanded)
%              Number of equality atoms :   85 ( 397 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t33_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_mcart_1 @ A @ B @ C @ D )
        = ( k4_mcart_1 @ E @ F @ G @ H ) )
     => ( ( A = E )
        & ( B = F )
        & ( C = G )
        & ( D = H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_mcart_1 @ A @ B @ C @ D )
          = ( k4_mcart_1 @ E @ F @ G @ H ) )
       => ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_mcart_1])).

thf('0',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('5',plain,(
    ! [X8: $i,X10: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X8 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = sk_H ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    sk_D = sk_H ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D ) ),
    inference(demod,[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('16',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_mcart_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X3 @ X2 @ X1 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('26',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i,X10: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X8 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('28',plain,
    ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_F ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X10: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X8 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,(
    sk_B = sk_F ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_F ) ),
    inference(demod,[status(thm)],['1','30'])).

thf('32',plain,
    ( $false
   <= ( sk_B != sk_F ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_D = sk_H ),
    inference(demod,[status(thm)],['7','8'])).

thf('34',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_D != sk_D )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X3 @ X2 @ X1 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('39',plain,(
    ! [X8: $i,X10: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X8 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = sk_G ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('43',plain,(
    sk_C = sk_G ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('49',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('51',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_B != sk_F )
    | ( sk_A != sk_E )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    sk_B != sk_F ),
    inference('sat_resolution*',[status(thm)],['36','46','54','55'])).

thf('57',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['32','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Uhba3XbBe
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 26 iterations in 0.015s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.46  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.46  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.46  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.46  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.46  thf(t33_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.46     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.20/0.46       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.20/0.46         ( ( D ) = ( H ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.46        ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.20/0.46          ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.20/0.46            ( ( D ) = ( H ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t33_mcart_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((((sk_A) != (sk_E))
% 0.20/0.46        | ((sk_B) != (sk_F))
% 0.20/0.46        | ((sk_C) != (sk_G))
% 0.20/0.46        | ((sk_D) != (sk_H)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.46         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.46         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d4_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.46       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k4_mcart_1 @ X0 @ X1 @ X2 @ X3)
% 0.20/0.46           = (k4_tarski @ (k3_mcart_1 @ X0 @ X1 @ X2) @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.46  thf(t7_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.46       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X8 : $i, X10 : $i]: ((k2_mcart_1 @ (k4_tarski @ X8 @ X10)) = (X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (((k2_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)) = (sk_H))),
% 0.20/0.46      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('9', plain, (((sk_D) = (sk_H))),
% 0.20/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.46         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k4_mcart_1 @ X0 @ X1 @ X2 @ X3)
% 0.20/0.46           = (k4_tarski @ (k3_mcart_1 @ X0 @ X1 @ X2) @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]: ((k1_mcart_1 @ (k4_tarski @ X8 @ X9)) = (X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.46           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (((k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.46         = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.20/0.46      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.46           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.20/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf(t31_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.46       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((k4_mcart_1 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X4 @ X5) @ X6) @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]: ((k1_mcart_1 @ (k4_tarski @ X8 @ X9)) = (X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.46           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X3 @ X2 @ X1)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]: ((k1_mcart_1 @ (k4_tarski @ X8 @ X9)) = (X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((k1_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.46         = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.46      inference('sup+', [status(thm)], ['16', '23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('26', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X8 : $i, X10 : $i]: ((k2_mcart_1 @ (k4_tarski @ X8 @ X10)) = (X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('28', plain, (((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_F))),
% 0.20/0.46      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X8 : $i, X10 : $i]: ((k2_mcart_1 @ (k4_tarski @ X8 @ X10)) = (X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('30', plain, (((sk_B) = (sk_F))),
% 0.20/0.46      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.46  thf('31', plain, ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (sk_F))))),
% 0.20/0.46      inference('demod', [status(thm)], ['1', '30'])).
% 0.20/0.46  thf('32', plain, (($false) <= (~ (((sk_B) = (sk_F))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.46  thf('33', plain, (((sk_D) = (sk_H))),
% 0.20/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('34', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('35', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_D) = (sk_H))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.46  thf('36', plain, ((((sk_D) = (sk_H)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.20/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf('38', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X3 @ X2 @ X1)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      (![X8 : $i, X10 : $i]: ((k2_mcart_1 @ (k4_tarski @ X8 @ X10)) = (X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('40', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.46  thf('41', plain,
% 0.20/0.46      (((k2_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)) = (sk_G))),
% 0.20/0.46      inference('sup+', [status(thm)], ['37', '40'])).
% 0.20/0.46  thf('42', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.46  thf('43', plain, (((sk_C) = (sk_G))),
% 0.20/0.46      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.46  thf('44', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('45', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (sk_G))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.46  thf('46', plain, ((((sk_C) = (sk_G)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.46  thf('47', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('48', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]: ((k1_mcart_1 @ (k4_tarski @ X8 @ X9)) = (X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('49', plain, (((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_E))),
% 0.20/0.46      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.46  thf('50', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]: ((k1_mcart_1 @ (k4_tarski @ X8 @ X9)) = (X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('51', plain, (((sk_A) = (sk_E))),
% 0.20/0.46      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.46  thf('52', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('53', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (sk_E))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.46  thf('54', plain, ((((sk_A) = (sk_E)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.46  thf('55', plain,
% 0.20/0.46      (~ (((sk_B) = (sk_F))) | ~ (((sk_A) = (sk_E))) | ~ (((sk_C) = (sk_G))) | 
% 0.20/0.46       ~ (((sk_D) = (sk_H)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('56', plain, (~ (((sk_B) = (sk_F)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['36', '46', '54', '55'])).
% 0.20/0.46  thf('57', plain, ($false),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['32', '56'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
