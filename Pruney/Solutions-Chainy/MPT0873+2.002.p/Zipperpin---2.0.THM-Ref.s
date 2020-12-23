%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HU8DmWlM6N

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:18 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 323 expanded)
%              Number of leaves         :   16 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  539 (3972 expanded)
%              Number of equality atoms :   98 ( 716 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

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
    | ( sk_C_2 != sk_G )
    | ( sk_D_2 != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_mcart_1 @ X14 @ X15 @ X16 @ X17 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(d2_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = D ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k2_mcart_1 @ X8 ) )
      | ( X11 = X12 )
      | ( X8
       != ( k4_tarski @ X13 @ X12 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_mcart_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ X13 @ X12 )
       != ( k4_tarski @ X9 @ X10 ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X12 ) )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k2_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) )
    = sk_H ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('11',plain,(
    sk_D_2 = sk_H ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D_2 ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D_2 ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_mcart_1 @ X14 @ X15 @ X16 @ X17 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(d1_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k1_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = C ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4
       != ( k1_mcart_1 @ X1 ) )
      | ( X4 = X5 )
      | ( X1
       != ( k4_tarski @ X5 @ X6 ) )
      | ( X1
       != ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ X5 @ X6 )
       != ( k4_tarski @ X2 @ X3 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ) )
    = sk_G ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('24',plain,(
    sk_C_2 = sk_G ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_C_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['16'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k4_tarski @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ) )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['16'])).

thf('32',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('34',plain,
    ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_F ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('36',plain,(
    sk_B = sk_F ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_F ) ),
    inference(demod,[status(thm)],['1','36'])).

thf('38',plain,
    ( $false
   <= ( sk_B != sk_F ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_D_2 = sk_H ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,
    ( ( sk_D_2 != sk_H )
   <= ( sk_D_2 != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( sk_D_2 != sk_D_2 )
   <= ( sk_D_2 != sk_H ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_D_2 = sk_H ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_C_2 = sk_G ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('44',plain,
    ( ( sk_C_2 != sk_G )
   <= ( sk_C_2 != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_C_2 != sk_G ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_C_2 = sk_G ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['16'])).

thf('49',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['16'])).

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
    | ( sk_C_2 != sk_G )
    | ( sk_D_2 != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    sk_B != sk_F ),
    inference('sat_resolution*',[status(thm)],['42','46','54','55'])).

thf('57',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['38','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HU8DmWlM6N
% 0.16/0.39  % Computer   : n022.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 10:46:11 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.26/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.26/0.55  % Solved by: fo/fo7.sh
% 0.26/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.26/0.55  % done 60 iterations in 0.050s
% 0.26/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.26/0.55  % SZS output start Refutation
% 0.26/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.26/0.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.26/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.26/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.26/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.26/0.55  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.26/0.55  thf(sk_H_type, type, sk_H: $i).
% 0.26/0.55  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.26/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.26/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.26/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.26/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.26/0.55  thf(t33_mcart_1, conjecture,
% 0.26/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.26/0.55     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.26/0.55       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.26/0.55         ( ( D ) = ( H ) ) ) ))).
% 0.26/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.26/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.26/0.55        ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.26/0.55          ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.26/0.55            ( ( D ) = ( H ) ) ) ) )),
% 0.26/0.55    inference('cnf.neg', [status(esa)], [t33_mcart_1])).
% 0.26/0.55  thf('0', plain,
% 0.26/0.55      ((((sk_A) != (sk_E))
% 0.26/0.55        | ((sk_B) != (sk_F))
% 0.26/0.55        | ((sk_C_2) != (sk_G))
% 0.26/0.55        | ((sk_D_2) != (sk_H)))),
% 0.26/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.55  thf('1', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.26/0.55      inference('split', [status(esa)], ['0'])).
% 0.26/0.55  thf('2', plain,
% 0.26/0.55      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2)
% 0.26/0.55         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.26/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.55  thf('3', plain,
% 0.26/0.55      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2)
% 0.26/0.55         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.26/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.55  thf(t31_mcart_1, axiom,
% 0.26/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.26/0.55     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.26/0.55       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.26/0.55  thf('4', plain,
% 0.26/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.26/0.55         ((k4_mcart_1 @ X14 @ X15 @ X16 @ X17)
% 0.26/0.55           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X14 @ X15) @ X16) @ X17))),
% 0.26/0.55      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.26/0.55  thf(d2_mcart_1, axiom,
% 0.26/0.55    (![A:$i]:
% 0.26/0.55     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.26/0.55       ( ![B:$i]:
% 0.26/0.55         ( ( ( B ) = ( k2_mcart_1 @ A ) ) <=>
% 0.26/0.55           ( ![C:$i,D:$i]:
% 0.26/0.55             ( ( ( A ) = ( k4_tarski @ C @ D ) ) => ( ( B ) = ( D ) ) ) ) ) ) ))).
% 0.26/0.55  thf('5', plain,
% 0.26/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.26/0.55         (((X11) != (k2_mcart_1 @ X8))
% 0.26/0.55          | ((X11) = (X12))
% 0.26/0.55          | ((X8) != (k4_tarski @ X13 @ X12))
% 0.26/0.55          | ((X8) != (k4_tarski @ X9 @ X10)))),
% 0.26/0.55      inference('cnf', [status(esa)], [d2_mcart_1])).
% 0.26/0.55  thf('6', plain,
% 0.26/0.55      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.26/0.55         (((k4_tarski @ X13 @ X12) != (k4_tarski @ X9 @ X10))
% 0.26/0.55          | ((k2_mcart_1 @ (k4_tarski @ X13 @ X12)) = (X12)))),
% 0.26/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.26/0.55  thf('7', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['6'])).
% 0.26/0.55  thf('8', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.55         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.26/0.55      inference('sup+', [status(thm)], ['4', '7'])).
% 0.26/0.55  thf('9', plain,
% 0.26/0.55      (((k2_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2)) = (sk_H))),
% 0.26/0.55      inference('sup+', [status(thm)], ['3', '8'])).
% 0.26/0.55  thf('10', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.55         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.26/0.55      inference('sup+', [status(thm)], ['4', '7'])).
% 0.26/0.55  thf('11', plain, (((sk_D_2) = (sk_H))),
% 0.26/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.26/0.55  thf('12', plain,
% 0.26/0.55      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2)
% 0.26/0.55         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D_2))),
% 0.26/0.55      inference('demod', [status(thm)], ['2', '11'])).
% 0.26/0.55  thf('13', plain,
% 0.26/0.55      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2)
% 0.26/0.55         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D_2))),
% 0.26/0.55      inference('demod', [status(thm)], ['2', '11'])).
% 0.26/0.55  thf('14', plain,
% 0.26/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.26/0.55         ((k4_mcart_1 @ X14 @ X15 @ X16 @ X17)
% 0.26/0.55           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X14 @ X15) @ X16) @ X17))),
% 0.26/0.55      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.26/0.55  thf(d1_mcart_1, axiom,
% 0.26/0.55    (![A:$i]:
% 0.26/0.55     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.26/0.55       ( ![B:$i]:
% 0.26/0.55         ( ( ( B ) = ( k1_mcart_1 @ A ) ) <=>
% 0.26/0.55           ( ![C:$i,D:$i]:
% 0.26/0.55             ( ( ( A ) = ( k4_tarski @ C @ D ) ) => ( ( B ) = ( C ) ) ) ) ) ) ))).
% 0.26/0.55  thf('15', plain,
% 0.26/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.26/0.55         (((X4) != (k1_mcart_1 @ X1))
% 0.26/0.55          | ((X4) = (X5))
% 0.26/0.55          | ((X1) != (k4_tarski @ X5 @ X6))
% 0.26/0.55          | ((X1) != (k4_tarski @ X2 @ X3)))),
% 0.26/0.55      inference('cnf', [status(esa)], [d1_mcart_1])).
% 0.26/0.55  thf('16', plain,
% 0.26/0.55      (![X2 : $i, X3 : $i, X5 : $i, X6 : $i]:
% 0.26/0.55         (((k4_tarski @ X5 @ X6) != (k4_tarski @ X2 @ X3))
% 0.26/0.55          | ((k1_mcart_1 @ (k4_tarski @ X5 @ X6)) = (X5)))),
% 0.26/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.26/0.55  thf('17', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['16'])).
% 0.26/0.55  thf('18', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.55         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.26/0.55           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.26/0.55      inference('sup+', [status(thm)], ['14', '17'])).
% 0.26/0.55  thf('19', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['6'])).
% 0.26/0.55  thf('20', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.55         ((k2_mcart_1 @ (k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))) = (X1))),
% 0.26/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.26/0.55  thf('21', plain,
% 0.26/0.55      (((k2_mcart_1 @ 
% 0.26/0.55         (k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2))) = (
% 0.26/0.55         sk_G))),
% 0.26/0.55      inference('sup+', [status(thm)], ['13', '20'])).
% 0.26/0.55  thf('22', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.55         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.26/0.55           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.26/0.55      inference('sup+', [status(thm)], ['14', '17'])).
% 0.26/0.55  thf('23', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['6'])).
% 0.26/0.55  thf('24', plain, (((sk_C_2) = (sk_G))),
% 0.26/0.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.26/0.55  thf('25', plain,
% 0.26/0.55      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2)
% 0.26/0.55         = (k4_mcart_1 @ sk_E @ sk_F @ sk_C_2 @ sk_D_2))),
% 0.26/0.55      inference('demod', [status(thm)], ['12', '24'])).
% 0.26/0.55  thf('26', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.55         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.26/0.55           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.26/0.55      inference('sup+', [status(thm)], ['14', '17'])).
% 0.26/0.55  thf('27', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['16'])).
% 0.26/0.55  thf('28', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.55         ((k1_mcart_1 @ (k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)))
% 0.26/0.55           = (k4_tarski @ X3 @ X2))),
% 0.26/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.26/0.55  thf('29', plain,
% 0.26/0.55      (((k1_mcart_1 @ 
% 0.26/0.55         (k1_mcart_1 @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2)))
% 0.26/0.55         = (k4_tarski @ sk_E @ sk_F))),
% 0.26/0.55      inference('sup+', [status(thm)], ['25', '28'])).
% 0.26/0.55  thf('30', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.55         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.26/0.55           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.26/0.55      inference('sup+', [status(thm)], ['14', '17'])).
% 0.26/0.55  thf('31', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['16'])).
% 0.26/0.55  thf('32', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.26/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.26/0.55  thf('33', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['6'])).
% 0.26/0.55  thf('34', plain, (((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_F))),
% 0.26/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.26/0.55  thf('35', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['6'])).
% 0.26/0.55  thf('36', plain, (((sk_B) = (sk_F))),
% 0.26/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.26/0.55  thf('37', plain, ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (sk_F))))),
% 0.26/0.55      inference('demod', [status(thm)], ['1', '36'])).
% 0.26/0.55  thf('38', plain, (($false) <= (~ (((sk_B) = (sk_F))))),
% 0.26/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.26/0.55  thf('39', plain, (((sk_D_2) = (sk_H))),
% 0.26/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.26/0.55  thf('40', plain, ((((sk_D_2) != (sk_H))) <= (~ (((sk_D_2) = (sk_H))))),
% 0.26/0.55      inference('split', [status(esa)], ['0'])).
% 0.26/0.55  thf('41', plain, ((((sk_D_2) != (sk_D_2))) <= (~ (((sk_D_2) = (sk_H))))),
% 0.26/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.26/0.55  thf('42', plain, ((((sk_D_2) = (sk_H)))),
% 0.26/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.26/0.55  thf('43', plain, (((sk_C_2) = (sk_G))),
% 0.26/0.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.26/0.55  thf('44', plain, ((((sk_C_2) != (sk_G))) <= (~ (((sk_C_2) = (sk_G))))),
% 0.26/0.55      inference('split', [status(esa)], ['0'])).
% 0.26/0.55  thf('45', plain, ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_C_2) = (sk_G))))),
% 0.26/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.26/0.55  thf('46', plain, ((((sk_C_2) = (sk_G)))),
% 0.26/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.26/0.55  thf('47', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.26/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.26/0.55  thf('48', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['16'])).
% 0.26/0.55  thf('49', plain, (((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_E))),
% 0.26/0.55      inference('sup+', [status(thm)], ['47', '48'])).
% 0.26/0.55  thf('50', plain,
% 0.26/0.55      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.26/0.55      inference('eq_res', [status(thm)], ['16'])).
% 0.26/0.55  thf('51', plain, (((sk_A) = (sk_E))),
% 0.26/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.26/0.55  thf('52', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.26/0.55      inference('split', [status(esa)], ['0'])).
% 0.26/0.55  thf('53', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (sk_E))))),
% 0.26/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.26/0.55  thf('54', plain, ((((sk_A) = (sk_E)))),
% 0.26/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.26/0.55  thf('55', plain,
% 0.26/0.55      (~ (((sk_B) = (sk_F))) | ~ (((sk_A) = (sk_E))) | 
% 0.26/0.55       ~ (((sk_C_2) = (sk_G))) | ~ (((sk_D_2) = (sk_H)))),
% 0.26/0.55      inference('split', [status(esa)], ['0'])).
% 0.26/0.55  thf('56', plain, (~ (((sk_B) = (sk_F)))),
% 0.26/0.55      inference('sat_resolution*', [status(thm)], ['42', '46', '54', '55'])).
% 0.26/0.55  thf('57', plain, ($false),
% 0.26/0.55      inference('simpl_trail', [status(thm)], ['38', '56'])).
% 0.26/0.55  
% 0.26/0.55  % SZS output end Refutation
% 0.26/0.55  
% 0.26/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
