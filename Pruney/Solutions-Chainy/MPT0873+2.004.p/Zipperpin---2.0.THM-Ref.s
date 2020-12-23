%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A8sAUqksLw

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 207 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  509 (2211 expanded)
%              Number of equality atoms :   91 ( 387 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_mcart_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k3_mcart_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('4',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_mcart_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k3_mcart_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3 = X2 )
      | ( ( k4_tarski @ X1 @ X3 )
       != ( k4_tarski @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_tarski @ X5 @ X4 ) )
      | ( X0 = X4 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != ( k4_tarski @ X1 @ X0 ) )
      | ( sk_H = X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
       != ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_H = X0 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    sk_H = sk_D ),
    inference(eq_res,[status(thm)],['9'])).

thf('11',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D ) ),
    inference(demod,[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_mcart_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k3_mcart_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( ( k4_tarski @ X1 @ X3 )
       != ( k4_tarski @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('18',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_mcart_1 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['13'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('24',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3 = X2 )
      | ( ( k4_tarski @ X1 @ X3 )
       != ( k4_tarski @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['25'])).

thf('27',plain,
    ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_F ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['25'])).

thf('29',plain,(
    sk_B = sk_F ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_F ) ),
    inference(demod,[status(thm)],['1','29'])).

thf('31',plain,
    ( $false
   <= ( sk_B != sk_F ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_H = sk_D ),
    inference(eq_res,[status(thm)],['9'])).

thf('33',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( sk_D != sk_D )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_mcart_1 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['25'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = sk_G ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('42',plain,(
    sk_C = sk_G ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['13'])).

thf('48',plain,
    ( ( '#_fresh_sk1' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['13'])).

thf('50',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_B != sk_F )
    | ( sk_A != sk_E )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    sk_B != sk_F ),
    inference('sat_resolution*',[status(thm)],['35','45','53','54'])).

thf('56',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['31','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A8sAUqksLw
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 43 iterations in 0.023s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.48  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.48  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.20/0.48  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(t33_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.48     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.20/0.48       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.20/0.48         ( ( D ) = ( H ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.48        ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.20/0.48          ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.20/0.48            ( ( D ) = ( H ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t33_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((sk_A) != (sk_E))
% 0.20/0.48        | ((sk_B) != (sk_F))
% 0.20/0.48        | ((sk_C) != (sk_G))
% 0.20/0.48        | ((sk_D) != (sk_H)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.48         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d4_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.48       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         ((k4_mcart_1 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.48           = (k4_tarski @ (k3_mcart_1 @ X7 @ X8 @ X9) @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.48         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         ((k4_mcart_1 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.48           = (k4_tarski @ (k3_mcart_1 @ X7 @ X8 @ X9) @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.48  thf(t33_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( k4_tarski @ A @ B ) = ( k4_tarski @ C @ D ) ) =>
% 0.20/0.48       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X3) = (X2)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (((k4_mcart_1 @ X3 @ X2 @ X1 @ X0) != (k4_tarski @ X5 @ X4))
% 0.20/0.48          | ((X0) = (X4)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k4_tarski @ X1 @ X0))
% 0.20/0.48          | ((sk_H) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.48            != (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48          | ((sk_H) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.48  thf('10', plain, (((sk_H) = (sk_D))),
% 0.20/0.48      inference('eq_res', [status(thm)], ['9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.48         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         ((k4_mcart_1 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.48           = (k4_tarski @ (k3_mcart_1 @ X7 @ X8 @ X9) @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X1) = (X0)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.20/0.48      inference('inj_rec', [status(thm)], ['13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['12', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((('#_fresh_sk1' @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.48         = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.20/0.48      inference('sup+', [status(thm)], ['11', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['12', '14'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf(d3_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ X4 @ X5 @ X6)
% 0.20/0.48           = (k4_tarski @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.20/0.48      inference('inj_rec', [status(thm)], ['13'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (('#_fresh_sk1' @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((('#_fresh_sk1' @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.48         = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.48      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (('#_fresh_sk1' @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('24', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X3) = (X2)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.20/0.48      inference('inj_rec', [status(thm)], ['25'])).
% 0.20/0.48  thf('27', plain, ((('#_fresh_sk2' @ (k4_tarski @ sk_A @ sk_B)) = (sk_F))),
% 0.20/0.48      inference('sup+', [status(thm)], ['24', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.20/0.48      inference('inj_rec', [status(thm)], ['25'])).
% 0.20/0.48  thf('29', plain, (((sk_B) = (sk_F))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (sk_F))))),
% 0.20/0.48      inference('demod', [status(thm)], ['1', '29'])).
% 0.20/0.48  thf('31', plain, (($false) <= (~ (((sk_B) = (sk_F))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.48  thf('32', plain, (((sk_H) = (sk_D))),
% 0.20/0.48      inference('eq_res', [status(thm)], ['9'])).
% 0.20/0.48  thf('33', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('34', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_D) = (sk_H))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain, ((((sk_D) = (sk_H)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ X4 @ X5 @ X6)
% 0.20/0.48           = (k4_tarski @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.20/0.48      inference('inj_rec', [status(thm)], ['25'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (('#_fresh_sk2' @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((('#_fresh_sk2' @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)) = (sk_G))),
% 0.20/0.48      inference('sup+', [status(thm)], ['36', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (('#_fresh_sk2' @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('42', plain, (((sk_C) = (sk_G))),
% 0.20/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('44', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (sk_G))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, ((((sk_C) = (sk_G)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.48  thf('46', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.20/0.48      inference('inj_rec', [status(thm)], ['13'])).
% 0.20/0.48  thf('48', plain, ((('#_fresh_sk1' @ (k4_tarski @ sk_A @ sk_B)) = (sk_E))),
% 0.20/0.48      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.20/0.48      inference('inj_rec', [status(thm)], ['13'])).
% 0.20/0.48  thf('50', plain, (((sk_A) = (sk_E))),
% 0.20/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('52', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (sk_E))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain, ((((sk_A) = (sk_E)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (~ (((sk_B) = (sk_F))) | ~ (((sk_A) = (sk_E))) | ~ (((sk_C) = (sk_G))) | 
% 0.20/0.48       ~ (((sk_D) = (sk_H)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('55', plain, (~ (((sk_B) = (sk_F)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['35', '45', '53', '54'])).
% 0.20/0.48  thf('56', plain, ($false),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['31', '55'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
