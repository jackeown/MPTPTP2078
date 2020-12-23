%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZwVfn5w98i

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 137 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  316 (1246 expanded)
%              Number of equality atoms :   63 ( 238 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t28_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k3_mcart_1 @ A @ B @ C )
          = ( k3_mcart_1 @ D @ E @ F ) )
       => ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_mcart_1])).

thf('0',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_mcart_1 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = sk_F ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('10',plain,(
    sk_C = sk_F ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_D @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_mcart_1 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('18',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['5'])).

thf('20',plain,
    ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X1 @ X3 ) )
      = X3 ) ),
    inference(inj_rec,[status(thm)],['5'])).

thf('22',plain,(
    sk_B = sk_E ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_E ) ),
    inference(demod,[status(thm)],['1','22'])).

thf('24',plain,
    ( $false
   <= ( sk_B != sk_E ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_C = sk_F ),
    inference(demod,[status(thm)],['8','9'])).

thf('26',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['13'])).

thf('31',plain,
    ( ( '#_fresh_sk1' @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['13'])).

thf('33',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_B != sk_E )
    | ( sk_A != sk_D )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    sk_B != sk_E ),
    inference('sat_resolution*',[status(thm)],['28','36','37'])).

thf('39',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['24','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZwVfn5w98i
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 24 iterations in 0.014s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.46  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.46  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.46  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(t28_mcart_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.46     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.21/0.46       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.46        ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.21/0.46          ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t28_mcart_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d3_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.46         ((k3_mcart_1 @ X4 @ X5 @ X6)
% 0.21/0.46           = (k4_tarski @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.46  thf(t33_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( ( k4_tarski @ A @ B ) = ( k4_tarski @ C @ D ) ) =>
% 0.21/0.46       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (((X3) = (X2)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.21/0.46      inference('inj_rec', [status(thm)], ['5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (('#_fresh_sk2' @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      ((('#_fresh_sk2' @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)) = (sk_F))),
% 0.21/0.46      inference('sup+', [status(thm)], ['3', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (('#_fresh_sk2' @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.46  thf('10', plain, (((sk_C) = (sk_F))),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_D @ sk_E @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['2', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.46         ((k3_mcart_1 @ X4 @ X5 @ X6)
% 0.21/0.46           = (k4_tarski @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (((X1) = (X0)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.21/0.46      inference('inj_rec', [status(thm)], ['13'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (('#_fresh_sk1' @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['12', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      ((('#_fresh_sk1' @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 0.21/0.46         = (k4_tarski @ sk_D @ sk_E))),
% 0.21/0.46      inference('sup+', [status(thm)], ['11', '15'])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (('#_fresh_sk1' @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['12', '14'])).
% 0.21/0.46  thf('18', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_D @ sk_E))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.21/0.46      inference('inj_rec', [status(thm)], ['5'])).
% 0.21/0.46  thf('20', plain, ((('#_fresh_sk2' @ (k4_tarski @ sk_A @ sk_B)) = (sk_E))),
% 0.21/0.46      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]: (('#_fresh_sk2' @ (k4_tarski @ X1 @ X3)) = (X3))),
% 0.21/0.46      inference('inj_rec', [status(thm)], ['5'])).
% 0.21/0.46  thf('22', plain, (((sk_B) = (sk_E))),
% 0.21/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf('23', plain, ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (sk_E))))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '22'])).
% 0.21/0.46  thf('24', plain, (($false) <= (~ (((sk_B) = (sk_E))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.46  thf('25', plain, (((sk_C) = (sk_F))),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('26', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('27', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (sk_F))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.46  thf('28', plain, ((((sk_C) = (sk_F)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.46  thf('29', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_D @ sk_E))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.21/0.46      inference('inj_rec', [status(thm)], ['13'])).
% 0.21/0.46  thf('31', plain, ((('#_fresh_sk1' @ (k4_tarski @ sk_A @ sk_B)) = (sk_D))),
% 0.21/0.46      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.46  thf('32', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.21/0.46      inference('inj_rec', [status(thm)], ['13'])).
% 0.21/0.46  thf('33', plain, (((sk_A) = (sk_D))),
% 0.21/0.46      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.46  thf('34', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('35', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (sk_D))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.46  thf('36', plain, ((((sk_A) = (sk_D)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.46  thf('37', plain,
% 0.21/0.46      (~ (((sk_B) = (sk_E))) | ~ (((sk_A) = (sk_D))) | ~ (((sk_C) = (sk_F)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('38', plain, (~ (((sk_B) = (sk_E)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['28', '36', '37'])).
% 0.21/0.46  thf('39', plain, ($false),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['24', '38'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
