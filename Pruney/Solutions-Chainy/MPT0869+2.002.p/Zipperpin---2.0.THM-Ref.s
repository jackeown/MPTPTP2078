%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Nlla97VWP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 123 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  295 (1092 expanded)
%              Number of equality atoms :   58 ( 196 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X3 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = sk_F ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    sk_C = sk_F ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_mcart_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_mcart_1 @ sk_D @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_mcart_1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('16',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X3 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('18',plain,
    ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_E ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X3 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,(
    sk_B = sk_E ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B != sk_E ) ),
    inference(demod,[status(thm)],['1','20'])).

thf('22',plain,
    ( $false
   <= ( sk_B != sk_E ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C = sk_F ),
    inference(demod,[status(thm)],['7','8'])).

thf('24',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( k4_tarski @ sk_A @ sk_B )
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('29',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('31',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_B != sk_E )
    | ( sk_A != sk_D )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    sk_B != sk_E ),
    inference('sat_resolution*',[status(thm)],['26','34','35'])).

thf('37',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['22','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Nlla97VWP
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 19 iterations in 0.013s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.44  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.44  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.44  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.44  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.44  thf(t28_mcart_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.44     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.20/0.44       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.44        ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.20/0.44          ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t28_mcart_1])).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('1', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.20/0.44      inference('split', [status(esa)], ['0'])).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(d3_mcart_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.44           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.44  thf(t7_mcart_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.44       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X3 : $i, X5 : $i]: ((k2_mcart_1 @ (k4_tarski @ X3 @ X5)) = (X5))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (((k2_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)) = (sk_F))),
% 0.20/0.44      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf('9', plain, (((sk_C) = (sk_F))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (((k3_mcart_1 @ sk_A @ sk_B @ sk_C) = (k3_mcart_1 @ sk_D @ sk_E @ sk_C))),
% 0.20/0.44      inference('demod', [status(thm)], ['2', '9'])).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.44           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i]: ((k1_mcart_1 @ (k4_tarski @ X3 @ X4)) = (X3))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.44      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (((k1_mcart_1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.44         = (k4_tarski @ sk_D @ sk_E))),
% 0.20/0.44      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.44      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.44  thf('16', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_D @ sk_E))),
% 0.20/0.44      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.44  thf('17', plain,
% 0.20/0.44      (![X3 : $i, X5 : $i]: ((k2_mcart_1 @ (k4_tarski @ X3 @ X5)) = (X5))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.44  thf('18', plain, (((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_E))),
% 0.20/0.44      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.44  thf('19', plain,
% 0.20/0.44      (![X3 : $i, X5 : $i]: ((k2_mcart_1 @ (k4_tarski @ X3 @ X5)) = (X5))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.44  thf('20', plain, (((sk_B) = (sk_E))),
% 0.20/0.44      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.44  thf('21', plain, ((((sk_B) != (sk_B))) <= (~ (((sk_B) = (sk_E))))),
% 0.20/0.44      inference('demod', [status(thm)], ['1', '20'])).
% 0.20/0.44  thf('22', plain, (($false) <= (~ (((sk_B) = (sk_E))))),
% 0.20/0.44      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.44  thf('23', plain, (((sk_C) = (sk_F))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('24', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.20/0.44      inference('split', [status(esa)], ['0'])).
% 0.20/0.44  thf('25', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (sk_F))))),
% 0.20/0.44      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.44  thf('26', plain, ((((sk_C) = (sk_F)))),
% 0.20/0.44      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.44  thf('27', plain, (((k4_tarski @ sk_A @ sk_B) = (k4_tarski @ sk_D @ sk_E))),
% 0.20/0.44      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.44  thf('28', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i]: ((k1_mcart_1 @ (k4_tarski @ X3 @ X4)) = (X3))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.44  thf('29', plain, (((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_D))),
% 0.20/0.44      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.44  thf('30', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i]: ((k1_mcart_1 @ (k4_tarski @ X3 @ X4)) = (X3))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.44  thf('31', plain, (((sk_A) = (sk_D))),
% 0.20/0.44      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.44  thf('32', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.20/0.44      inference('split', [status(esa)], ['0'])).
% 0.20/0.44  thf('33', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (sk_D))))),
% 0.20/0.44      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.44  thf('34', plain, ((((sk_A) = (sk_D)))),
% 0.20/0.44      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.44  thf('35', plain,
% 0.20/0.44      (~ (((sk_B) = (sk_E))) | ~ (((sk_A) = (sk_D))) | ~ (((sk_C) = (sk_F)))),
% 0.20/0.44      inference('split', [status(esa)], ['0'])).
% 0.20/0.44  thf('36', plain, (~ (((sk_B) = (sk_E)))),
% 0.20/0.44      inference('sat_resolution*', [status(thm)], ['26', '34', '35'])).
% 0.20/0.44  thf('37', plain, ($false),
% 0.20/0.44      inference('simpl_trail', [status(thm)], ['22', '36'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
