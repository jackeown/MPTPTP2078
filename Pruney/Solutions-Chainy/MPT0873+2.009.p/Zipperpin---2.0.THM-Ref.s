%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZgNm5b3cJQ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:19 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 292 expanded)
%              Number of leaves         :   15 (  86 expanded)
%              Depth                    :   17
%              Number of atoms          :  462 (3157 expanded)
%              Number of equality atoms :   83 ( 541 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_mcart_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3 = X2 )
      | ( ( k4_tarski @ X1 @ X3 )
       != ( k4_tarski @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( '#_fresh_sk2' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    = sk_H ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('10',plain,(
    sk_D = sk_H ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D ) ),
    inference(demod,[status(thm)],['2','10'])).

thf('12',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D ) ),
    inference(demod,[status(thm)],['2','10'])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_mcart_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X4 @ X5 ) @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( ( k4_tarski @ X1 @ X3 )
       != ( k4_tarski @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['5'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( '#_fresh_sk2' @ ( '#_fresh_sk1' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    = sk_G ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('21',plain,(
    sk_C = sk_G ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_mcart_1 @ sk_E @ sk_F @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['14'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k4_tarski @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( '#_fresh_sk1' @ ( '#_fresh_sk1' @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k4_tarski @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['5'])).

thf('30',plain,
    ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_F ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['5'])).

thf('32',plain,(
    sk_B = sk_F ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_F ) ),
    inference(demod,[status(thm)],['1','32'])).

thf('34',plain,
    ( $false
   <= ( sk_B != sk_F ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_D = sk_H ),
    inference(demod,[status(thm)],['8','9'])).

thf('36',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( sk_D != sk_D )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_C = sk_G ),
    inference(demod,[status(thm)],['19','20'])).

thf('40',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['14'])).

thf('45',plain,
    ( ( '#_fresh_sk1' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['14'])).

thf('47',plain,(
    sk_A = sk_E ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_E ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A = sk_E ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_B != sk_F )
    | ( sk_A != sk_E )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    sk_B != sk_F ),
    inference('sat_resolution*',[status(thm)],['38','42','50','51'])).

thf('53',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['34','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZgNm5b3cJQ
% 0.17/0.37  % Computer   : n022.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 12:53:56 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 50 iterations in 0.030s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.24/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.24/0.51  thf(sk_H_type, type, sk_H: $i).
% 0.24/0.51  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.24/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.24/0.51  thf(t33_mcart_1, conjecture,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.24/0.51     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.24/0.51       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.24/0.51         ( ( D ) = ( H ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.24/0.51        ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.24/0.51          ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.24/0.51            ( ( D ) = ( H ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t33_mcart_1])).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      ((((sk_A) != (sk_E))
% 0.24/0.51        | ((sk_B) != (sk_F))
% 0.24/0.51        | ((sk_C) != (sk_G))
% 0.24/0.51        | ((sk_D) != (sk_H)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('1', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.24/0.51      inference('split', [status(esa)], ['0'])).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.51         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.51         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t31_mcart_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.24/0.51       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.51         ((k4_mcart_1 @ X4 @ X5 @ X6 @ X7)
% 0.24/0.51           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X4 @ X5) @ X6) @ X7))),
% 0.24/0.51      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.24/0.51  thf(t33_zfmisc_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51     ( ( ( k4_tarski @ A @ B ) = ( k4_tarski @ C @ D ) ) =>
% 0.24/0.51       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (((X3) = (X2)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.24/0.51      inference('inj_rec', [status(thm)], ['5'])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (('#_fresh_sk2' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.24/0.51      inference('sup+', [status(thm)], ['4', '6'])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      ((('#_fresh_sk2' @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)) = (sk_H))),
% 0.24/0.51      inference('sup+', [status(thm)], ['3', '7'])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (('#_fresh_sk2' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.24/0.51      inference('sup+', [status(thm)], ['4', '6'])).
% 0.24/0.51  thf('10', plain, (((sk_D) = (sk_H))),
% 0.24/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.51         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D))),
% 0.24/0.51      inference('demod', [status(thm)], ['2', '10'])).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.51         = (k4_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_D))),
% 0.24/0.51      inference('demod', [status(thm)], ['2', '10'])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.51         ((k4_mcart_1 @ X4 @ X5 @ X6 @ X7)
% 0.24/0.51           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X4 @ X5) @ X6) @ X7))),
% 0.24/0.51      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (((X1) = (X0)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.24/0.51      inference('inj_rec', [status(thm)], ['14'])).
% 0.24/0.51  thf('16', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.24/0.51           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.24/0.51      inference('sup+', [status(thm)], ['13', '15'])).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.24/0.51      inference('inj_rec', [status(thm)], ['5'])).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (('#_fresh_sk2' @ ('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)))
% 0.24/0.51           = (X1))),
% 0.24/0.51      inference('sup+', [status(thm)], ['16', '17'])).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      ((('#_fresh_sk2' @ 
% 0.24/0.51         ('#_fresh_sk1' @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))) = (
% 0.24/0.51         sk_G))),
% 0.24/0.51      inference('sup+', [status(thm)], ['12', '18'])).
% 0.24/0.51  thf('20', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (('#_fresh_sk2' @ ('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)))
% 0.24/0.51           = (X1))),
% 0.24/0.51      inference('sup+', [status(thm)], ['16', '17'])).
% 0.24/0.51  thf('21', plain, (((sk_C) = (sk_G))),
% 0.24/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.24/0.51  thf('22', plain,
% 0.24/0.51      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.51         = (k4_mcart_1 @ sk_E @ sk_F @ sk_C @ sk_D))),
% 0.24/0.51      inference('demod', [status(thm)], ['11', '21'])).
% 0.24/0.51  thf('23', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.24/0.51           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.24/0.51      inference('sup+', [status(thm)], ['13', '15'])).
% 0.24/0.51  thf('24', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.24/0.51      inference('inj_rec', [status(thm)], ['14'])).
% 0.24/0.51  thf('25', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (('#_fresh_sk1' @ ('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)))
% 0.24/0.51           = (k4_tarski @ X3 @ X2))),
% 0.24/0.51      inference('sup+', [status(thm)], ['23', '24'])).
% 0.24/0.51  thf('26', plain,
% 0.24/0.51      ((('#_fresh_sk1' @ 
% 0.24/0.51         ('#_fresh_sk1' @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.24/0.51         = (k4_tarski @ sk_E @ sk_F))),
% 0.24/0.51      inference('sup+', [status(thm)], ['22', '25'])).
% 0.24/0.51  thf('27', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         (('#_fresh_sk1' @ ('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)))
% 0.24/0.51           = (k4_tarski @ X3 @ X2))),
% 0.24/0.51      inference('sup+', [status(thm)], ['23', '24'])).
% 0.24/0.51  thf('28', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.24/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.24/0.51  thf('29', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.24/0.51      inference('inj_rec', [status(thm)], ['5'])).
% 0.24/0.51  thf('30', plain, ((('#_fresh_sk2' @ (k4_tarski @ sk_A @ sk_B)) = (sk_F))),
% 0.24/0.51      inference('sup+', [status(thm)], ['28', '29'])).
% 0.24/0.51  thf('31', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.24/0.51      inference('inj_rec', [status(thm)], ['5'])).
% 0.24/0.51  thf('32', plain, (((sk_B) = (sk_F))),
% 0.24/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.24/0.51  thf('33', plain, ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (sk_F))))),
% 0.24/0.51      inference('demod', [status(thm)], ['1', '32'])).
% 0.24/0.51  thf('34', plain, (($false) <= (~ (((sk_B) = (sk_F))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.24/0.51  thf('35', plain, (((sk_D) = (sk_H))),
% 0.24/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.24/0.51  thf('36', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.24/0.51      inference('split', [status(esa)], ['0'])).
% 0.24/0.51  thf('37', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_D) = (sk_H))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.24/0.51  thf('38', plain, ((((sk_D) = (sk_H)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.24/0.51  thf('39', plain, (((sk_C) = (sk_G))),
% 0.24/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.24/0.51  thf('40', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.24/0.51      inference('split', [status(esa)], ['0'])).
% 0.24/0.51  thf('41', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (sk_G))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.24/0.51  thf('42', plain, ((((sk_C) = (sk_G)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.24/0.51  thf('43', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_E @ sk_F))),
% 0.24/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.24/0.51  thf('44', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.24/0.51      inference('inj_rec', [status(thm)], ['14'])).
% 0.24/0.51  thf('45', plain, ((('#_fresh_sk1' @ (k4_tarski @ sk_A @ sk_B)) = (sk_E))),
% 0.24/0.51      inference('sup+', [status(thm)], ['43', '44'])).
% 0.24/0.51  thf('46', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.24/0.51      inference('inj_rec', [status(thm)], ['14'])).
% 0.24/0.51  thf('47', plain, (((sk_A) = (sk_E))),
% 0.24/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.24/0.51  thf('48', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.24/0.51      inference('split', [status(esa)], ['0'])).
% 0.24/0.51  thf('49', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (sk_E))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.24/0.51  thf('50', plain, ((((sk_A) = (sk_E)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.24/0.51  thf('51', plain,
% 0.24/0.51      (~ (((sk_B) = (sk_F))) | ~ (((sk_A) = (sk_E))) | ~ (((sk_C) = (sk_G))) | 
% 0.24/0.51       ~ (((sk_D) = (sk_H)))),
% 0.24/0.51      inference('split', [status(esa)], ['0'])).
% 0.24/0.51  thf('52', plain, (~ (((sk_B) = (sk_F)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['38', '42', '50', '51'])).
% 0.24/0.51  thf('53', plain, ($false),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['34', '52'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
