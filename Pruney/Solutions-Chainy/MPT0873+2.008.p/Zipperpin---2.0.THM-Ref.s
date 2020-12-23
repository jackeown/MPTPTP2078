%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ilKBVlaqYT

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 303 expanded)
%              Number of leaves         :   20 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  499 (3319 expanded)
%              Number of equality atoms :   91 ( 575 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf('#_fresh_sk5_type',type,(
    '#_fresh_sk5': $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf('#_fresh_sk4_type',type,(
    '#_fresh_sk4': $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_mcart_1 @ ( k4_tarski @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t32_mcart_1])).

thf(t28_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X5 = X4 )
      | ( ( k3_mcart_1 @ X5 @ X8 @ X9 )
       != ( k3_mcart_1 @ X4 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('4',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk3' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X5 ) ),
    inference(inj_rec,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk3' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( '#_fresh_sk3' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk3' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('8',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( ( k4_tarski @ X1 @ X3 )
       != ( k4_tarski @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['9'])).

thf('11',plain,
    ( ( '#_fresh_sk1' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['9'])).

thf('13',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_A @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3 = X2 )
      | ( ( k4_tarski @ X1 @ X3 )
       != ( k4_tarski @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['16'])).

thf('18',plain,
    ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_F ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['16'])).

thf('20',plain,(
    sk_B = sk_F ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_A @ sk_B @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_A @ sk_B @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_mcart_1 @ ( k4_tarski @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t32_mcart_1])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8 = X6 )
      | ( ( k3_mcart_1 @ X5 @ X8 @ X9 )
       != ( k3_mcart_1 @ X4 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('25',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk4' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X8 ) ),
    inference(inj_rec,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk4' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( '#_fresh_sk4' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = sk_G ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk4' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('29',plain,(
    sk_C = sk_G ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_H ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_mcart_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_mcart_1 @ ( k4_tarski @ X10 @ X11 ) @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t32_mcart_1])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X9 = X7 )
      | ( ( k3_mcart_1 @ X5 @ X8 @ X9 )
       != ( k3_mcart_1 @ X4 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('33',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk5' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X9 ) ),
    inference(inj_rec,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk5' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( '#_fresh_sk5' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = sk_H ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk5' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('37',plain,(
    sk_D = sk_H ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    sk_B = sk_F ),
    inference(demod,[status(thm)],['18','19'])).

thf('41',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['38'])).

thf('42',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['11','12'])).

thf('45',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['38'])).

thf('46',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_C = sk_G ),
    inference(demod,[status(thm)],['27','28'])).

thf('49',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['38'])).

thf('50',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_D != sk_H )
    | ( sk_C != sk_G )
    | ( sk_A != sk_E )
    | ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['38'])).

thf('53',plain,(
    sk_D != sk_H ),
    inference('sat_resolution*',[status(thm)],['43','47','51','52'])).

thf('54',plain,(
    sk_D != sk_H ),
    inference(simpl_trail,[status(thm)],['39','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ilKBVlaqYT
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:32 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 39 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.47  thf('#_fresh_sk3_type', type, '#_fresh_sk3': $i > $i).
% 0.20/0.47  thf('#_fresh_sk5_type', type, '#_fresh_sk5': $i > $i).
% 0.20/0.47  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.47  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf('#_fresh_sk4_type', type, '#_fresh_sk4': $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.47  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(t33_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.47     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.20/0.47       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.20/0.47         ( ( D ) = ( H ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.47        ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.20/0.47          ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.20/0.47            ( ( D ) = ( H ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t33_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t32_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47       ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.47           = (k3_mcart_1 @ (k4_tarski @ X10 @ X11) @ X12 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t32_mcart_1])).
% 0.20/0.47  thf(t28_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.47     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.20/0.47       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (((X5) = (X4))
% 0.20/0.47          | ((k3_mcart_1 @ X5 @ X8 @ X9) != (k3_mcart_1 @ X4 @ X6 @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (('#_fresh_sk3' @ (k3_mcart_1 @ X5 @ X8 @ X9)) = (X5))),
% 0.20/0.47      inference('inj_rec', [status(thm)], ['3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (('#_fresh_sk3' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.47           = (k4_tarski @ X3 @ X2))),
% 0.20/0.47      inference('sup+', [status(thm)], ['2', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((('#_fresh_sk3' @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.47         = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.47      inference('sup+', [status(thm)], ['1', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (('#_fresh_sk3' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.47           = (k4_tarski @ X3 @ X2))),
% 0.20/0.47      inference('sup+', [status(thm)], ['2', '4'])).
% 0.20/0.47  thf('8', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t33_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( k4_tarski @ A @ B ) = ( k4_tarski @ C @ D ) ) =>
% 0.20/0.47       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (((X1) = (X0)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.20/0.47      inference('inj_rec', [status(thm)], ['9'])).
% 0.20/0.47  thf('11', plain, ((('#_fresh_sk1' @ (k4_tarski @ sk_A @ sk_B)) = (sk_E))),
% 0.20/0.47      inference('sup+', [status(thm)], ['8', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.20/0.47      inference('inj_rec', [status(thm)], ['9'])).
% 0.20/0.47  thf('13', plain, (((sk_A) = (sk_E))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47         = (k4_mcart_1 @ sk_A @ sk_F @ sk_G @ sk_H))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '13'])).
% 0.20/0.47  thf('15', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (((X3) = (X2)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.20/0.47      inference('inj_rec', [status(thm)], ['16'])).
% 0.20/0.47  thf('18', plain, ((('#_fresh_sk2' @ (k4_tarski @ sk_A @ sk_B)) = (sk_F))),
% 0.20/0.47      inference('sup+', [status(thm)], ['15', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.20/0.47      inference('inj_rec', [status(thm)], ['16'])).
% 0.20/0.47  thf('20', plain, (((sk_B) = (sk_F))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47         = (k4_mcart_1 @ sk_A @ sk_B @ sk_G @ sk_H))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47         = (k4_mcart_1 @ sk_A @ sk_B @ sk_G @ sk_H))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '20'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.47           = (k3_mcart_1 @ (k4_tarski @ X10 @ X11) @ X12 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t32_mcart_1])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (((X8) = (X6))
% 0.20/0.47          | ((k3_mcart_1 @ X5 @ X8 @ X9) != (k3_mcart_1 @ X4 @ X6 @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (('#_fresh_sk4' @ (k3_mcart_1 @ X5 @ X8 @ X9)) = (X8))),
% 0.20/0.47      inference('inj_rec', [status(thm)], ['24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (('#_fresh_sk4' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['23', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((('#_fresh_sk4' @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)) = (sk_G))),
% 0.20/0.47      inference('sup+', [status(thm)], ['22', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (('#_fresh_sk4' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['23', '25'])).
% 0.20/0.47  thf('29', plain, (((sk_C) = (sk_G))),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.47         = (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_H))),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.47           = (k3_mcart_1 @ (k4_tarski @ X10 @ X11) @ X12 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t32_mcart_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (((X9) = (X7))
% 0.20/0.47          | ((k3_mcart_1 @ X5 @ X8 @ X9) != (k3_mcart_1 @ X4 @ X6 @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (('#_fresh_sk5' @ (k3_mcart_1 @ X5 @ X8 @ X9)) = (X9))),
% 0.20/0.47      inference('inj_rec', [status(thm)], ['32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (('#_fresh_sk5' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['31', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((('#_fresh_sk5' @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)) = (sk_H))),
% 0.20/0.47      inference('sup+', [status(thm)], ['30', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (('#_fresh_sk5' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['31', '33'])).
% 0.20/0.47  thf('37', plain, (((sk_D) = (sk_H))),
% 0.20/0.47      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((((sk_A) != (sk_E))
% 0.20/0.47        | ((sk_B) != (sk_F))
% 0.20/0.47        | ((sk_C) != (sk_G))
% 0.20/0.47        | ((sk_D) != (sk_H)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('39', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.20/0.47      inference('split', [status(esa)], ['38'])).
% 0.20/0.47  thf('40', plain, (((sk_B) = (sk_F))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('41', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.20/0.47      inference('split', [status(esa)], ['38'])).
% 0.20/0.47  thf('42', plain, ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (sk_F))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.47  thf('43', plain, ((((sk_B) = (sk_F)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.47  thf('44', plain, (((sk_A) = (sk_E))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('45', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.20/0.47      inference('split', [status(esa)], ['38'])).
% 0.20/0.47  thf('46', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (sk_E))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain, ((((sk_A) = (sk_E)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.47  thf('48', plain, (((sk_C) = (sk_G))),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('49', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.20/0.47      inference('split', [status(esa)], ['38'])).
% 0.20/0.47  thf('50', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (sk_G))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.47  thf('51', plain, ((((sk_C) = (sk_G)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (~ (((sk_D) = (sk_H))) | ~ (((sk_C) = (sk_G))) | ~ (((sk_A) = (sk_E))) | 
% 0.20/0.47       ~ (((sk_B) = (sk_F)))),
% 0.20/0.47      inference('split', [status(esa)], ['38'])).
% 0.20/0.47  thf('53', plain, (~ (((sk_D) = (sk_H)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['43', '47', '51', '52'])).
% 0.20/0.47  thf('54', plain, (((sk_D) != (sk_H))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['39', '53'])).
% 0.20/0.47  thf('55', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['37', '54'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.34/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
